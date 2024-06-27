use std::{borrow::Cow, collections::HashSet, ops::ControlFlow, rc::Rc};

use rustc_interface::{
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
            visit::{TyContext, Visitor},VarDebugInfo,
            BasicBlock, Body, CallReturnPlaces, HasLocalDecls, Local, Location, Operand, Place,
            ProjectionElem, Promoted, Rvalue, Statement, StatementKind, Terminator,
            TerminatorEdges, TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
        ty::{self, Region, RegionKind, RegionVid, TyCtxt, TypeVisitor},
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::domain::RegionAbstraction,
    rustc_interface,
    utils::{self, PlaceRepacker},
};

use super::domain::{Borrow, BorrowKind, BorrowsState, MaybeOldPlace};

pub struct BorrowsEngine<'mir, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    location_table: &'mir LocationTable,
    input_facts: &'mir PoloniusInput,
    borrow_set: Rc<BorrowSet<'tcx>>,
    region_inference_context: Rc<RegionInferenceContext<'tcx>>,
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

    fn tag_deref_of_place_with_location(
        &self,
        state: &mut BorrowsState<'tcx>,
        place: utils::Place<'tcx>,
        location: Location,
    ) {
        state.borrows = state
            .borrows
            .clone()
            .into_iter()
            .map(|mut borrow| {
                if borrow.borrowed_place.place().is_deref_of(place) {
                    borrow.borrowed_place = MaybeOldPlace::OldPlace {
                        place: borrow.borrowed_place.place(),
                        before: location,
                    };
                }
                borrow
            })
            .collect();
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

    fn loans_invalidated_at(&self, location: Location, start: bool) -> Vec<BorrowIndex> {
        self.input_facts
            .loan_invalidated_at
            .iter()
            .filter_map(
                |(loan_point, loan)| match self.location_table.to_location(*loan_point) {
                    RichLocation::Start(loan_location) if loan_location == location && start => Some(*loan),
                    RichLocation::Mid(loan_location) if loan_location == location && !start => Some(*loan),
                    _ => None,
                },
            )
            .collect()
    }

    fn loan_issued_at_location(&self, location: Location, start: bool) -> Option<BorrowIndex> {
        self.input_facts
            .loan_issued_at
            .iter()
            .find_map(
                |(_, loan, loan_point)| match self.location_table.to_location(*loan_point) {
                    RichLocation::Start(loan_location) if loan_location == location && start => Some(*loan),
                    RichLocation::Mid(loan_location) if loan_location == location && !start => Some(*loan),
                    _ => None,
                },
            )
    }

    fn placed_loaned_to_place(&self, place: Place<'tcx>) -> Vec<Place<'tcx>> {
        self.borrow_set
            .location_map
            .iter()
            .filter(|(_, borrow)| borrow.assigned_place == place)
            .map(|(_, borrow)| borrow.borrowed_place)
            .collect()
    }

    fn remove_loans_assigned_to(
        &self,
        state: &mut BorrowsState<'tcx>,
        assigned_to: Place<'tcx>,
    ) -> FxHashSet<Borrow<'tcx>> {
        let (to_remove, to_keep): (FxHashSet<_>, FxHashSet<_>) = state
            .borrows
            .clone()
            .into_iter()
            .partition(|borrow| borrow.assigned_place.place() == assigned_to.into());

        state.borrows = to_keep;

        to_remove
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsDomain<'tcx> {
    before_start: BorrowsState<'tcx>,
    before_after: BorrowsState<'tcx>,
    start: BorrowsState<'tcx>,
    pub after: BorrowsState<'tcx>,
}

impl<'tcx> BorrowsDomain<'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({
            "before_start": self.before_start.to_json(repacker),
            "before_after": self.before_after.to_json(repacker),
            "start": self.start.to_json(repacker),
            "after": self.after.to_json(repacker),
        })
    }

    pub fn new() -> Self {
        Self {
            before_start: BorrowsState::new(),
            before_after: BorrowsState::new(),
            start: BorrowsState::new(),
            after: BorrowsState::new(),
        }
    }

    fn apply_to_end_state(&mut self, action: BorrowAction<'_, 'tcx>) {
        self.after.apply_action(action)
    }

    pub fn actions<'a>(&'a self, start: bool) -> Vec<BorrowAction<'a, 'tcx>> {
        let (s, e) = if start {
            (&self.before_start, &self.start)
        } else {
            (&self.before_after, &self.after)
        };
        let mut actions = vec![];
        for borrow in s.borrows.iter() {
            if !e.contains_borrow(borrow) {
                actions.push(BorrowAction::RemoveBorrow(borrow));
            }
        }
        for borrow in e.borrows.iter() {
            if !s.contains_borrow(borrow) {
                actions.push(BorrowAction::AddBorrow(Cow::Borrowed(borrow)));
            }
        }
        actions
    }
}

#[derive(Debug, Clone)]
pub enum BorrowAction<'state, 'tcx> {
    AddBorrow(Cow<'state, Borrow<'tcx>>),
    RemoveBorrow(&'state Borrow<'tcx>),
}

impl <'state, 'tcx> BorrowAction<'state, 'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            BorrowAction::AddBorrow(borrow) => json!({
                "action": "AddBorrow",
                "borrow": borrow.to_json(repacker)
            }),
            BorrowAction::RemoveBorrow(borrow) => json!({
                "action": "RemoveBorrow",
                "borrow": borrow.to_json(repacker)
            }),
        }
    }

}

impl<'tcx> JoinSemiLattice for BorrowsDomain<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        self.after.join(&other.after)
    }
}

impl<'tcx, 'a> AnalysisDomain<'tcx> for BorrowsEngine<'a, 'tcx> {
    type Domain = BorrowsDomain<'tcx>;
    type Direction = Forward;
    const NAME: &'static str = "borrows";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        todo!()
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        todo!()
    }
}

fn get_location(rich_location: RichLocation) -> Location {
    match rich_location {
        RichLocation::Start(location) => location,
        RichLocation::Mid(location) => location,
    }
}

impl<'tcx, 'a> Analysis<'tcx> for BorrowsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.before_start = state.after.clone();
        for loan in self.loans_invalidated_at(location, true) {
            state.after.remove_rustc_borrow(&loan);
        }
        if let Some(loan) = self.loan_issued_at_location(location, true) {
            state.after.add_rustc_borrow(loan, &self.borrow_set);
        }
        state.before_after = state.after.clone();
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.start = state.after.clone();
        for loan in self.loans_invalidated_at(location, false) {
            state.after.remove_rustc_borrow(&loan);
        }
        if let Some(loan) = self.loan_issued_at_location(location, false) {
            state.after.add_rustc_borrow(loan, &self.borrow_set);
        }
        match &statement.kind {
            StatementKind::Assign(box (target, rvalue)) => match rvalue {
                Rvalue::Use(Operand::Move(from)) => {
                    for mut borrow in self.remove_loans_assigned_to(&mut state.after, *target) {
                        borrow.assigned_place = MaybeOldPlace::OldPlace {
                            place: (*target).into(),
                            before: location,
                        };
                        state.after.add_borrow(borrow);
                        // state.log_action(format!(
                        //     "Removed loan assigned to {:?} due to move {:?} -> {:?}:  {:?}",
                        //     target, from, target, borrow
                        // ));
                    }
                    let loans_to_move = self.remove_loans_assigned_to(&mut state.after, *from);
                    for loan in loans_to_move {
                        state.after.add_borrow(Borrow::new(
                            BorrowKind::PCS,
                            loan.borrowed_place.place(),
                            (*target).into(),
                            loan.is_mut
                        ));
                    }
                    self.tag_deref_of_place_with_location(
                        &mut state.after,
                        (*target).into(),
                        location,
                    );
                }
                _ => {}
            },
            StatementKind::StorageDead(local) => {
                state.after.borrows.retain(|borrow| {
                    if borrow.assigned_place.place().local == *local {
                        false
                    } else {
                        true
                    }
                });
            }
            _ => {}
        }
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        state.before_start = state.after.clone();
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                fn_span,
            } => {
                for dest_region in self.get_regions_in(
                    destination.ty(self.body.local_decls(), self.tcx).ty,
                    location,
                ) {
                    let mut region_abstraction = RegionAbstraction::new();
                    region_abstraction.add_loan_out(*destination);
                    for arg in args.iter() {
                        for arg_region in
                            self.get_regions_in(arg.ty(self.body.local_decls(), self.tcx), location)
                        {
                            if self.outlives_or_eq(arg_region, dest_region) {
                                for origin_place in
                                    self.placed_loaned_to_place(arg.place().unwrap())
                                {
                                    region_abstraction.add_loan_in(origin_place);
                                }
                            }
                        }
                    }
                    eprintln!("Add RA {:?}", region_abstraction);
                    state.after.add_region_abstraction(region_abstraction);
                }
            }
            _ => {}
        }
        state.before_after = state.after.clone();
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        state.start = state.after.clone();
        match &terminator.kind {
            TerminatorKind::Call { args, .. } => {
                for arg in args {
                    if let Operand::Move(arg) = arg {
                        self.remove_loans_assigned_to(&mut state.after, *arg);
                    }
                }
            }
            _ => {}
        }
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
