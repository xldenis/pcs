use std::{borrow::Cow, collections::HashSet, ops::ControlFlow, rc::Rc};

use rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, RegionInferenceContext, RichLocation,
        },
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{Analysis, AnalysisDomain, Forward, JoinSemiLattice},
    index::IndexVec,
    middle::{
        mir::{
            visit::{TyContext, Visitor},
            BasicBlock, Body, CallReturnPlaces, HasLocalDecls, Local, Location, Operand, Place,
            ProjectionElem, Promoted, Rvalue, Statement, StatementKind, Terminator,
            TerminatorEdges, TerminatorKind, VarDebugInfo, RETURN_PLACE, START_BLOCK,
        },
        ty::{self, Region, RegionKind, RegionVid, TyCtxt, TypeVisitor},
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::domain::RegionAbstraction,
    combined_pcs::UnblockGraph,
    rustc_interface,
    utils::{self, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::borrows_state::BorrowsState;
use super::domain::{Borrow, DerefExpansion, MaybeOldPlace, Reborrow};

pub struct BorrowsEngine<'mir, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    location_table: &'mir LocationTable,
    input_facts: &'mir PoloniusInput,
    borrow_set: Rc<BorrowSet<'tcx>>,
    region_inference_context: Rc<RegionInferenceContext<'tcx>>,
}

struct BorrowsVisitor<'tcx, 'mir, 'state> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    state: &'state mut BorrowsDomain<'mir, 'tcx>,
    input_facts: &'mir PoloniusInput,
    location_table: &'mir LocationTable,
    borrow_set: Rc<BorrowSet<'tcx>>,
    before: bool,
    preparing: bool,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(self.body, self.tcx)
    }
    pub fn preparing(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, before, true)
    }

    pub fn applying(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, before, false)
    }

    fn new(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
        preparing: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor {
            tcx: engine.tcx,
            body: engine.body,
            state,
            input_facts: engine.input_facts,
            before,
            preparing,
            location_table: engine.location_table,
            borrow_set: engine.borrow_set.clone(),
        }
    }
    fn ensure_expansion_to(&mut self, place: utils::Place<'tcx>, location: Location) {
        self.state.after.ensure_expansion_to(
            self.tcx,
            self.body,
            MaybeOldPlace::Current { place },
            location,
        )
    }

    fn loans_invalidated_at(&self, location: Location, start: bool) -> Vec<BorrowIndex> {
        self.input_facts
            .loan_invalidated_at
            .iter()
            .filter_map(
                |(loan_point, loan)| match self.location_table.to_location(*loan_point) {
                    RichLocation::Start(loan_location) if loan_location == location && start => {
                        Some(*loan)
                    }
                    RichLocation::Mid(loan_location) if loan_location == location && !start => {
                        Some(*loan)
                    }
                    _ => None,
                },
            )
            .collect()
    }
}

impl<'tcx, 'mir, 'state> Visitor<'tcx> for BorrowsVisitor<'tcx, 'mir, 'state> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.before {
            // TODO: also self.preparing?
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if place.is_owned(self.body, self.tcx) && place.is_ref(self.body, self.tcx) {
                        self.ensure_expansion_to(place.project_deref(self.repacker()), location);
                    } else {
                        self.ensure_expansion_to(place, location);
                    }
                }
                _ => {}
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if !self.before && !self.preparing {
            match &terminator.kind {
                TerminatorKind::Call { args, .. } => {
                    for arg in args {
                        if let Operand::Move(arg) = arg {
                            self.state.after.remove_loans_assigned_to(
                                self.tcx,
                                &self.borrow_set,
                                (*arg).into(),
                                location.block,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);

        if self.preparing {
            for loan in self.loans_invalidated_at(location, self.before) {
                self.state.after.remove_rustc_borrow(
                    self.tcx,
                    &loan,
                    &self.borrow_set,
                    &self.body,
                    location.block,
                );
            }
        }

        // Stuff in this block will be included as the middle "bridge" ops that
        // are visible to Prusti
        if self.preparing && !self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, _)) => {
                    self.ensure_expansion_to((*target).into(), location);
                }
                StatementKind::StorageDead(local) => {
                    let place: utils::Place<'tcx> = (*local).into();
                    let repacker = PlaceRepacker::new(self.body, self.tcx);
                    if place.ty(repacker).ty.is_ref() {
                        self.state.after.make_deref_of_place_old(place, repacker);
                        // self.state.after.deref_expansions.delete(place.into());
                    }
                }
                _ => {}
            }
        }

        // Will be included as start bridge ops
        if self.preparing && self.before {
            match &statement.kind {
                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if place.is_owned(self.body, self.tcx) && place.is_ref(self.body, self.tcx) {
                        self.ensure_expansion_to(place.project_deref(self.repacker()), location);
                    } else {
                        self.ensure_expansion_to(place, location);
                    }
                }
                _ => {}
            }
        }

        if !self.preparing && !self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    if target.ty(self.body, self.tcx).ty.is_ref() {
                        let target = (*target).into();
                        self.state.after.make_deref_of_place_old(
                            target,
                            PlaceRepacker::new(self.body, self.tcx),
                        );
                        self.state.after.ensure_expansion_to(
                            self.tcx,
                            self.body,
                            MaybeOldPlace::Current {
                                place: target.project_deref(self.repacker()),
                            },
                            location,
                        );
                    }
                    self.state.after.set_latest((*target).into(), location);
                    match rvalue {
                        Rvalue::Use(Operand::Move(from)) => {
                            if matches!(from.ty(self.body, self.tcx).ty.kind(), ty::TyKind::Ref(_, _, r) if r.is_mut())
                            {
                                let from: utils::Place<'tcx> = (*from).into();
                                let target: utils::Place<'tcx> = (*target).into();

                                // let mut ug = UnblockGraph::new();
                                // ug.unblock_place(
                                //     from.project_deref(self.repacker()).into(),
                                //     &self.state.after,
                                //     location.block,
                                // );
                                // self.state.after.apply_unblock_graph(ug);

                                self.state.after.move_reborrows(
                                    from.project_deref(self.repacker()),
                                    target.project_deref(self.repacker()),
                                );

                                self.state.after.make_deref_of_place_old(
                                    from,
                                    PlaceRepacker::new(self.body, self.tcx),
                                );
                            }
                        }
                        Rvalue::Use(Operand::Copy(from)) => {
                            if from.ty(self.body, self.tcx).ty.is_ref() {
                                let from: utils::Place<'tcx> = (*from).into();
                                let target: utils::Place<'tcx> = (*target).into();
                                self.state.after.add_reborrow(
                                    from.project_deref(self.repacker()),
                                    target.project_deref(self.repacker()),
                                    Mutability::Not,
                                    location,
                                )
                            }
                        }
                        Rvalue::Ref(_, kind, blocked_place) => {
                            let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            let assigned_place = target.project_deref(self.repacker());
                            assert_eq!(
                                self.tcx
                                    .erase_regions((*blocked_place).ty(self.body, self.tcx).ty),
                                self.tcx
                                    .erase_regions((*assigned_place).ty(self.body, self.tcx).ty)
                            );
                            self.state.after.add_reborrow(
                                blocked_place,
                                assigned_place,
                                kind.mutability(),
                                location,
                            );
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
        use Rvalue::*;
        match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | CheckedBinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => {}

            &Ref(_, _, place)
            | &AddressOf(_, place)
            | &Len(place)
            | &Discriminant(place)
            | &CopyForDeref(place) => {
                if self.before {
                    self.ensure_expansion_to(place.into(), location);
                }
            }
        }
    }
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        location_table: &'mir LocationTable,
        input_facts: &'mir PoloniusInput,
        borrow_set: Rc<BorrowSet<'tcx>>,
        region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            location_table,
            input_facts,
            borrow_set,
            region_inference_context,
        }
    }

    fn get_regions_in(&self, ty: ty::Ty<'tcx>, location: Location) -> HashSet<RegionVid> {
        struct RegionVisitor(HashSet<RegionVid>);

        impl<'tcx> ty::TypeVisitor<ty::TyCtxt<'tcx>> for RegionVisitor {
            fn visit_region(&mut self, region: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
                match region.kind() {
                    RegionKind::ReEarlyBound(_) => todo!(),
                    RegionKind::ReLateBound(_, _) => todo!(),
                    RegionKind::ReFree(_) => todo!(),
                    RegionKind::ReStatic => todo!(),
                    RegionKind::ReVar(vid) => {
                        self.0.insert(vid);
                    }
                    RegionKind::RePlaceholder(_) => todo!(),
                    RegionKind::ReErased => todo!(),
                    RegionKind::ReError(_) => todo!(),
                }
                ControlFlow::Continue(())
            }
        }
        let mut visitor = RegionVisitor(HashSet::new());
        visitor.visit_ty(ty);
        visitor.0
    }

    fn placed_loaned_to_place(&self, place: Place<'tcx>) -> Vec<Place<'tcx>> {
        self.borrow_set
            .location_map
            .iter()
            .filter(|(_, borrow)| borrow.assigned_place == place)
            .map(|(_, borrow)| borrow.borrowed_place)
            .collect()
    }

    fn outlives_or_eq(&self, sup: RegionVid, sub: RegionVid) -> bool {
        if sup == sub {
            true
        } else {
            self.region_inference_context
                .outlives_constraints()
                .any(|constraint| {
                    sup == constraint.sup
                        && (sub == constraint.sub || self.outlives_or_eq(constraint.sub, sub))
                })
        }
    }
}

#[derive(Clone, Debug)]
pub enum ReborrowAction<'tcx> {
    AddReborrow(Reborrow<'tcx>),
    RemoveReborrow(Reborrow<'tcx>),
    ExpandPlace(DerefExpansion<'tcx>),
    CollapsePlace(Vec<utils::Place<'tcx>>, MaybeOldPlace<'tcx>),
}

impl<'tcx> ReborrowAction<'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            ReborrowAction::AddReborrow(reborrow) => json!({
                "action": "AddReborrow",
                "reborrow": reborrow.to_json(repacker)
            }),
            ReborrowAction::RemoveReborrow(reborrow) => json!({
                "action": "RemoveReborrow",
                "reborrow": reborrow.to_json(repacker)
            }),
            ReborrowAction::ExpandPlace(e) => json!({
                "action": "ExpandPlace",
                "place": e.base.to_json(repacker),
            }),
            ReborrowAction::CollapsePlace(_, place) => json!({
                "action": "CollapsePlace",
                "place": place.to_json(repacker),
            }),
        }
    }
}

impl<'mir, 'tcx> JoinSemiLattice for BorrowsDomain<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        self.after.join(&other.after)
    }
}

impl<'tcx, 'a> AnalysisDomain<'tcx> for BorrowsEngine<'a, 'tcx> {
    type Domain = BorrowsDomain<'a, 'tcx>;
    type Direction = Forward;
    const NAME: &'static str = "borrows";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        todo!()
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        todo!()
    }
}

impl<'a, 'tcx> Analysis<'tcx> for BorrowsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, true).visit_statement(statement, location);
        state.before_start = state.after.clone();
        BorrowsVisitor::applying(self, state, true).visit_statement(statement, location);
        state.before_after = state.after.clone();
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, false).visit_statement(statement, location);
        state.start = state.after.clone();
        BorrowsVisitor::applying(self, state, false).visit_statement(statement, location);
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, true).visit_terminator(terminator, location);
        state.before_start = state.after.clone();
        BorrowsVisitor::applying(self, state, true).visit_terminator(terminator, location);
        state.before_after = state.after.clone();
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        BorrowsVisitor::preparing(self, state, false).visit_terminator(terminator, location);
        state.start = state.after.clone();
        BorrowsVisitor::applying(self, state, false).visit_terminator(terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        state: &mut Self::Domain,
        block: BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        todo!()
    }
}
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsDomain<'mir, 'tcx> {
    pub before_start: BorrowsState<'mir, 'tcx>,
    pub before_after: BorrowsState<'mir, 'tcx>,
    pub start: BorrowsState<'mir, 'tcx>,
    pub after: BorrowsState<'mir, 'tcx>,
}

impl<'mir, 'tcx> BorrowsDomain<'mir, 'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'mir, 'tcx>) -> Value {
        json!({
            "before_start": self.before_start.to_json(repacker),
            "before_after": self.before_after.to_json(repacker),
            "start": self.start.to_json(repacker),
            "after": self.after.to_json(repacker),
        })
    }

    pub fn new(body: &'mir Body<'tcx>) -> Self {
        Self {
            before_start: BorrowsState::new(body),
            before_after: BorrowsState::new(body),
            start: BorrowsState::new(body),
            after: BorrowsState::new(body),
        }
    }
}
