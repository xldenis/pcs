use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, HashSet},
    ops::ControlFlow,
    rc::Rc,
};

use polonius_engine::FactTypes;
use rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
            RichLocation, RustcFacts,
        },
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{Analysis, AnalysisDomain, Forward, JoinSemiLattice},
    index::IndexVec,
    middle::{
        mir::{
            self,
            visit::{TyContext, Visitor},
            AggregateKind, BasicBlock, Body, BorrowKind, CallReturnPlaces, ConstantKind,
            HasLocalDecls, Local, Location, Operand, Place, ProjectionElem, Promoted, Rvalue,
            Statement, StatementKind, Terminator, TerminatorEdges, TerminatorKind, VarDebugInfo,
            RETURN_PLACE, START_BLOCK,
        },
        ty::{
            self, EarlyBinder, Region, RegionKind, RegionVid, TyCtxt, TypeVisitable, TypeVisitor,
        },
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::{
        borrows_state::RegionProjectionMember,
        domain::{AbstractionBlockEdge, AbstractionTarget, RegionProjection},
        region_abstraction::RegionAbstraction,
    },
    rustc_interface,
    utils::{self, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::{
    borrows_state::{BorrowsState, RegionProjectionMemberDirection},
    domain::AbstractionType,
    engine::{BorrowsDomain, BorrowsEngine},
};
use super::{
    domain::{Borrow, MaybeOldPlace, Reborrow},
    unblock_graph::UnblockGraph,
};

#[derive(Debug, Clone, Copy)]
pub struct DebugCtx {
    pub location: Location,
}

pub struct BorrowsVisitor<'tcx, 'mir, 'state> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    state: &'state mut BorrowsDomain<'mir, 'tcx>,
    input_facts: &'mir PoloniusInput,
    location_table: &'mir LocationTable,
    borrow_set: Rc<BorrowSet<'tcx>>,
    before: bool,
    preparing: bool,
    region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    debug_ctx: Option<DebugCtx>,
    output_facts: &'mir PoloniusOutput,
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
            region_inference_context: engine.region_inference_context.clone(),
            debug_ctx: None,
            output_facts: engine.output_facts,
        }
    }
    fn ensure_expansion_to_exactly(&mut self, place: utils::Place<'tcx>, location: Location) {
        self.state
            .after
            .ensure_expansion_to_exactly(self.tcx, self.body, place, location)
    }

    fn subsets_at(
        &self,
        location: Location,
        start: bool,
    ) -> BTreeMap<RegionVid, BTreeSet<RegionVid>> {
        let location = if start {
            self.location_table.start_index(location)
        } else {
            self.location_table.mid_index(location)
        };
        self.output_facts.subsets_at(location).into_owned()
    }

    fn origins_containing_loans_at(&self, location: Location, start: bool) -> Vec<RegionVid> {
        let location = if start {
            self.location_table.start_index(location)
        } else {
            self.location_table.mid_index(location)
        };
        self.output_facts
            .origin_contains_loan_at(location)
            .iter()
            .filter(|(_, loans)| !loans.is_empty())
            .map(|(origin, _)| origin.to_owned())
            .collect()
    }

    fn origins_live_at(&self, location: Location, start: bool) -> &[RegionVid] {
        let location = if start {
            self.location_table.start_index(location)
        } else {
            self.location_table.mid_index(location)
        };
        self.output_facts.origins_live_at(location)
    }

    fn loans_invalidated_at(&self, location: Location, start: bool) -> Vec<BorrowIndex> {
        let location = if start {
            self.location_table.start_index(location)
        } else {
            self.location_table.mid_index(location)
        };
        self.input_facts
            .loan_invalidated_at
            .iter()
            .filter_map(|(loan_point, loan)| {
                if *loan_point == location {
                    Some(*loan)
                } else {
                    None
                }
            })
            .collect()
    }

    fn outlives(&self, sup: RegionVid, sub: RegionVid) -> bool {
        for o in self
            .region_inference_context
            .outlives_constraints()
            .filter(|c| c.sup == sup)
        {
            if o.sub == sub {
                return true;
            } else if self.outlives(o.sub, sub) {
                return true;
            }
        }
        false
    }

    fn construct_region_abstraction_if_necessary(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        location: Location,
    ) {
        let (func_def_id, substs) = match func {
            Operand::Constant(c) => match c.literal {
                ConstantKind::Val(_, ty) => match ty.kind() {
                    ty::TyKind::FnDef(def_id, substs) => (def_id, substs),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        let sig = EarlyBinder::instantiate_identity(self.tcx.fn_sig(func_def_id));
        let sig = self.tcx.liberate_late_bound_regions(*func_def_id, sig);
        let output_lifetimes = extract_lifetimes(sig.output());
        if output_lifetimes.is_empty() {
            return;
        }
        let param_env = self.tcx.param_env(func_def_id);
        let mut edges = vec![];

        for (idx, ty) in sig.inputs().iter().enumerate() {
            let input_place: utils::Place<'tcx> = args[idx].place().unwrap().into();
            let ty = match ty.kind() {
                ty::TyKind::Ref(region, ty, Mutability::Mut) => {
                    for output in self.matches_for_input_lifetime(
                        *region,
                        param_env,
                        substs,
                        sig.output(),
                        destination.into(),
                    ) {
                        let input_place = input_place.project_deref(self.repacker());
                        edges.push((
                            idx,
                            AbstractionBlockEdge {
                                input: AbstractionTarget::MaybeOldPlace(input_place.into()),
                                output,
                            },
                        ));
                    }
                    *ty
                }
                _ => *ty,
            };
            for (lifetime_idx, input_lifetime) in extract_lifetimes(ty).into_iter().enumerate() {
                for output in self.matches_for_input_lifetime(
                    input_lifetime,
                    param_env,
                    substs,
                    sig.output(),
                    destination.into(),
                ) {
                    edges.push((
                        idx,
                        AbstractionBlockEdge {
                            input: AbstractionTarget::RegionProjection(
                                input_place.region_projection(lifetime_idx, self.repacker()),
                            ),
                            output,
                        },
                    ));
                }
            }
        }
        assert!(edges.len() > 0, "No edges for {:?}", func_def_id);
        self.state
            .after
            .add_region_abstraction(RegionAbstraction::new(AbstractionType::FunctionCall {
                def_id: *func_def_id,
                location,
                substs,
                edges,
            }), location.block);
    }

    fn matches_for_input_lifetime(
        &self,
        input_lifetime: ty::Region<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        substs: ty::GenericArgsRef<'tcx>,
        output_ty: ty::Ty<'tcx>,
        output_place: utils::Place<'tcx>,
    ) -> Vec<AbstractionTarget<'tcx>> {
        let mut result = vec![];
        let output_ty = match output_ty.kind() {
            ty::TyKind::Ref(output_lifetime, ty, Mutability::Mut) => {
                if outlives_in_param_env(input_lifetime, *output_lifetime, param_env) {
                    result.push(AbstractionTarget::MaybeOldPlace(
                        output_place.project_deref(self.repacker()).into(),
                    ));
                }
                *ty
            }
            _ => output_ty,
        };
        for (output_lifetime_idx, output_lifetime) in
            extract_lifetimes(output_ty).into_iter().enumerate()
        {
            if outlives_in_param_env(input_lifetime, output_lifetime, param_env) {
                result.push(AbstractionTarget::RegionProjection(
                    output_place.region_projection(output_lifetime_idx, self.repacker()),
                ));
            }
        }
        result
    }
}
fn get_vid_from_substs<'tcx>(
    region: ty::Region<'tcx>,
    substs: ty::GenericArgsRef<'tcx>,
) -> RegionVid {
    match region.kind() {
        ty::RegionKind::ReEarlyBound(early_bound) => {
            get_vid(&substs[early_bound.index as usize].expect_region()).unwrap()
        }
        _ => todo!(),
    }
}

fn outlives_in_param_env<'tcx>(
    input_lifetime: ty::Region<'tcx>,
    output_lifetime: ty::Region<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> bool {
    if input_lifetime == output_lifetime {
        return true;
    }
    for bound in param_env.caller_bounds() {
        match bound.as_region_outlives_clause() {
            Some(outlives) => {
                let outlives = outlives.no_bound_vars().unwrap();
                if outlives.0 == input_lifetime && outlives.1 == output_lifetime {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

pub fn get_vid(region: &Region) -> Option<RegionVid> {
    match region.kind() {
        RegionKind::ReVar(vid) => Some(vid),
        other => None,
    }
}

impl<'tcx, 'mir, 'state> Visitor<'tcx> for BorrowsVisitor<'tcx, 'mir, 'state> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.before && self.preparing {
            match operand {
                Operand::Move(place) => {
                    self.state.after.set_latest((*place).into(), location);
                    self.state.after.make_place_old(
                        (*place).into(),
                        PlaceRepacker::new(self.body, self.tcx),
                        None,
                    );
                }
                _ => {}
            }
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    self.ensure_expansion_to_exactly(place, location);
                }
                _ => {}
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        if !self.before && !self.preparing {
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    self.construct_region_abstraction_if_necessary(
                        func,
                        args,
                        (*destination).into(),
                        location,
                    );
                }
                _ => {}
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        if self.preparing {
            let mut g = UnblockGraph::new();

            for loan in self.loans_invalidated_at(location, self.before) {
                let borrow = &self.borrow_set[loan];
                let borrow = Borrow::new(
                    borrow.borrowed_place.into(),
                    borrow.assigned_place.into(),
                    matches!(borrow.kind, BorrowKind::Mut { .. }),
                );
                g.unblock_place(
                    MaybeOldPlace::Current {
                        place: borrow.borrowed_place.into(),
                    },
                    &self.state.after,
                    location.block,
                    self.repacker(),
                );
            }

            let live_origins = self.origins_live_at(location, self.before);

            for abstraction in self.state.after.region_abstractions().iter() {
                if abstraction
                    .outputs()
                    .iter()
                    .all(|i| !live_origins.contains(&i.region(self.repacker())))
                {
                    g.kill_abstraction(
                        &self.state.after,
                        &abstraction.abstraction_type,
                        self.repacker(),
                    );
                }
            }

            self.state.after.apply_unblock_graph(g, self.tcx);
        }

        // Stuff in this block will be included as the middle "bridge" ops that
        // are visible to Prusti
        if self.preparing && !self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, _)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    if !target.is_owned(self.body, self.tcx) {
                        self.ensure_expansion_to_exactly(target, location);
                    }
                }
                _ => {}
            }
        }

        // Will be included as start bridge ops
        if self.preparing && self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    if target.ty(self.body, self.tcx).ty.is_ref() {
                        let target = (*target).into();
                        self.state.after.make_place_old(
                            target,
                            PlaceRepacker::new(self.body, self.tcx),
                            self.debug_ctx,
                        );
                    }
                }
                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.body, self.tcx) {
                        if place.is_ref(self.body, self.tcx) {
                            self.ensure_expansion_to_exactly(
                                place.project_deref(self.repacker()),
                                location,
                            );
                        } else {
                            self.ensure_expansion_to_exactly(place, location);
                        }
                    }
                }
                _ => {}
            }
        }

        if !self.preparing && !self.before {
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    self.debug_ctx = Some(DebugCtx { location });
                    let place: utils::Place<'tcx> = (*local).into();
                    let repacker = PlaceRepacker::new(self.body, self.tcx);
                    if place.ty(repacker).ty.is_ref() {
                        self.state
                            .after
                            .make_place_old(place, repacker, self.debug_ctx);
                    }
                }
                StatementKind::Assign(box (target, rvalue)) => {
                    self.state.after.set_latest((*target).into(), location);
                    match rvalue {
                        Rvalue::Aggregate(box kind, fields) => match kind {
                            AggregateKind::Adt(def_id, variant_idx, substs, _, _) => {
                                let target: utils::Place<'tcx> = (*target).into();
                                for (idx, field) in fields.iter_enumerated() {
                                    match field.ty(self.body, self.tcx).kind() {
                                        ty::TyKind::Ref(region, _, _) => {
                                            for proj in target.region_projections(self.repacker()) {
                                                if self
                                                    .outlives(get_vid(region).unwrap(), proj.region)
                                                {
                                                    let operand_place: utils::Place<'tcx> =
                                                        field.place().unwrap().into();
                                                    let operand_place = MaybeOldPlace::new(
                                                        operand_place
                                                            .project_deref(self.repacker()),
                                                        Some(location),
                                                    );
                                                    self.state.after.add_region_projection_member(
                                                        RegionProjectionMember::new(
                                                            operand_place,
                                                            proj,
                                                            location,
                                                            RegionProjectionMemberDirection::PlaceIsRegionInput,
                                                        ),
                                                    );
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        },
                        Rvalue::Use(Operand::Move(from)) => {
                            let repacker = PlaceRepacker::new(self.body, self.tcx);
                            let from: utils::Place<'tcx> = (*from).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            if matches!(from.ty(self.repacker()).ty.kind(), ty::TyKind::Ref(_, _, r) if r.is_mut())
                            {
                                self.state.after.move_reborrows(
                                    MaybeOldPlace::new(
                                        from.project_deref(self.repacker()),
                                        Some(self.state.after.get_latest(&from)),
                                    ),
                                    target.project_deref(self.repacker()).into(),
                                );
                            }
                            self.state.after.move_region_projection_member_projections(
                                MaybeOldPlace::Current { place: from },
                                MaybeOldPlace::Current { place: target },
                                repacker,
                            );
                            let mut ug = UnblockGraph::new();
                            for d in self
                                .state
                                .after
                                .deref_expansions()
                                .descendants_of_place(from.into())
                            {
                                ug.kill_place(
                                    d.base(),
                                    &self.state.after,
                                    location.block,
                                    self.repacker(),
                                );
                            }
                            self.state.after.apply_unblock_graph(ug, self.tcx);
                        }
                        Rvalue::Use(Operand::Copy(from)) => {
                            match from.ty(self.body, self.tcx).ty.kind() {
                                ty::TyKind::Ref(region, _, _) => {
                                    let from: utils::Place<'tcx> = (*from).into();
                                    let target: utils::Place<'tcx> = (*target).into();
                                    self.state.after.add_reborrow(
                                        from.project_deref(self.repacker()),
                                        target.project_deref(self.repacker()),
                                        Mutability::Not,
                                        location,
                                        *region, // TODO: This is the region for the place, not the loan, does that matter?
                                    );
                                }
                                _ => {}
                            }
                        }
                        Rvalue::Ref(region, kind, blocked_place) => {
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
                                *region,
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
                let place: utils::Place<'tcx> = place.into();
                if self.before && self.preparing && !place.is_owned(self.body, self.tcx) {
                    self.ensure_expansion_to_exactly(place, location);
                }
            }
        }
    }
}

struct LifetimeExtractor<'tcx> {
    lifetimes: Vec<ty::Region<'tcx>>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_region(&mut self, rr: ty::Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        self.lifetimes.push(rr);
        ControlFlow::Continue(())
    }
}

pub fn extract_lifetimes<'tcx>(ty: ty::Ty<'tcx>) -> Vec<ty::Region<'tcx>> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    visitor.lifetimes
}

pub fn extract_nested_lifetimes<'tcx>(ty: ty::Ty<'tcx>) -> Vec<ty::Region<'tcx>> {
    match ty.kind() {
        ty::TyKind::Ref(_, ty, _) => extract_lifetimes(*ty),
        _ => extract_lifetimes(ty),
    }
}
