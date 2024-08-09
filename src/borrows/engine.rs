use std::{borrow::Cow, collections::HashSet, ops::ControlFlow, rc::Rc};

use rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
            RichLocation,
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
    rustc_interface,
    utils::{self, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::{
    borrows_state::BorrowsState, borrows_visitor::BorrowsVisitor, path_condition::PathCondition,
};
use super::{
    deref_expansion::DerefExpansion,
    domain::{Borrow, MaybeOldPlace, Reborrow},
    path_condition::PathConditions,
};

pub struct BorrowsEngine<'mir, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'mir Body<'tcx>,
    pub location_table: &'mir LocationTable,
    pub input_facts: &'mir PoloniusInput,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub output_facts: &'mir PoloniusOutput,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        location_table: &'mir LocationTable,
        input_facts: &'mir PoloniusInput,
        borrow_set: Rc<BorrowSet<'tcx>>,
        region_inference_context: Rc<RegionInferenceContext<'tcx>>,
        output_facts: &'mir PoloniusOutput,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            location_table,
            input_facts,
            borrow_set,
            region_inference_context,
            output_facts,
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
                "place": e.base().to_json(repacker),
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
        let mut other_after = other.after.clone();

        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let pc = PathCondition::new(other.block, self.block);
        other_after.add_path_condition(pc);

        // Overlay both graphs
        self.after.join(&other_after)
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
    pub block: BasicBlock,
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

    pub fn new(body: &'mir Body<'tcx>, block: BasicBlock) -> Self {
        Self {
            before_start: BorrowsState::new(body),
            before_after: BorrowsState::new(body),
            start: BorrowsState::new(body),
            after: BorrowsState::new(body),
            block,
        }
    }
}
