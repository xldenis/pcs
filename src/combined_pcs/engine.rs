// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use itertools::Itertools;
use rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{self, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{Analysis, AnalysisDomain},
    index::{Idx, IndexVec},
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, PlaceElem,
            Promoted, Rvalue, Statement, StatementKind, Terminator, TerminatorEdges, RETURN_PLACE,
            START_BLOCK,
        },
        ty::{RegionVid, TyCtxt},
    },
};

use crate::{
    borrows::{
        borrows_state::BorrowsState,
        deref_expansions::DerefExpansions,
        domain::{AbstractionType, MaybeOldPlace, Reborrow},
        engine::{BorrowsEngine, ReborrowAction},
    },
    free_pcs::{
        engine::FpcsEngine, CapabilityKind, CapabilityLocal, CapabilitySummary,
        FreePlaceCapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceOrdering, PlaceRepacker},
    visualization::generate_unblock_dot_graph,
};

use super::domain::PlaceCapabilitySummary;

pub struct BodyWithBorrowckFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub location_table: Option<Rc<LocationTable>>,
    pub input_facts: Option<Box<PoloniusInput>>,
    pub output_facts: Option<Rc<PoloniusOutput>>,
}

impl<'tcx> From<consumers::BodyWithBorrowckFacts<'tcx>> for BodyWithBorrowckFacts<'tcx> {
    fn from(value: consumers::BodyWithBorrowckFacts<'tcx>) -> Self {
        Self {
            body: value.body,
            promoted: value.promoted,
            borrow_set: value.borrow_set,
            region_inference_context: value.region_inference_context,
            location_table: value.location_table.map(Rc::new),
            input_facts: value.input_facts,
            output_facts: value.output_facts,
        }
    }
}

pub struct PcsContext<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub mir: &'a BodyWithBorrowckFacts<'tcx>,
}

impl<'a, 'tcx> PcsContext<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, mir: &'a BodyWithBorrowckFacts<'tcx>) -> Self {
        let rp = PlaceRepacker::new(&mir.body, tcx);
        Self { rp, mir }
    }
}

pub struct PcsEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<PcsContext<'a, 'tcx>>,
    block: Cell<BasicBlock>,

    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) borrows: BorrowsEngine<'a, 'tcx>,
}
impl<'a, 'tcx> PcsEngine<'a, 'tcx> {
    pub fn new(cgx: PcsContext<'a, 'tcx>) -> Self {
        let cgx = Rc::new(cgx);
        let fpcs = FpcsEngine(cgx.rp);
        let borrows = BorrowsEngine::new(
            cgx.rp.tcx(),
            cgx.rp.body(),
            cgx.mir.location_table.as_ref().unwrap(),
            cgx.mir.input_facts.as_ref().unwrap(),
            cgx.mir.borrow_set.clone(),
            cgx.mir.region_inference_context.clone(),
            cgx.mir.output_facts.as_ref().unwrap(),
        );
        Self {
            cgx,
            block: Cell::new(START_BLOCK),
            fpcs,
            borrows,
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for PcsEngine<'a, 'tcx> {
    type Domain = PlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        let block = self.block.get();
        self.block.set(block.plus(1));
        PlaceCapabilitySummary::new(self.cgx.clone(), block)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.block.set(START_BLOCK);
        state.fpcs.initialize_as_start_block();
        // Initialize borrows if needed
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct ProjectionEdge<'tcx> {
    pub blockers: Vec<PlaceElem<'tcx>>,
    pub blocked: MaybeOldPlace<'tcx>,
}

impl<'tcx> ProjectionEdge<'tcx> {
    pub fn blocks_place(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.blocked == place
    }
    pub fn blocker_places(&self, tcx: TyCtxt<'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        self.blockers
            .iter()
            .map(|p| self.blocked.project_deeper(tcx, *p))
            .collect()
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct AbstractionEdge<'tcx> {
    abstraction_type: AbstractionType<'tcx>,
}

impl<'tcx> AbstractionEdge<'tcx> {
    /// Terminating the region makes these places accessible
    pub fn blocked_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocks_places()
    }

    pub fn abstraction_type(&self) -> &AbstractionType<'tcx> {
        &self.abstraction_type
    }

    pub fn location(&self) -> Location {
        self.abstraction_type.location()
    }

    /// Capabilities to these places must be given up to make the blocked places
    /// accessible
    pub fn blocker_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocker_places()
    }

    pub fn new(abstraction_type: AbstractionType<'tcx>) -> Self {
        Self { abstraction_type }
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub enum UnblockEdgeType<'tcx> {
    Reborrow {
        is_mut: bool,
        /// Terminating the reborrow requires this place to expire
        blocker: MaybeOldPlace<'tcx>,
        /// Terminating the reborrow makes this place available
        blocked: MaybeOldPlace<'tcx>,
    },
    Projection(ProjectionEdge<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
}

#[derive(Debug, Eq, PartialEq)]
pub enum UnblockAction<'tcx> {
    TerminateAbstraction(Location, AbstractionType<'tcx>),
    TerminateReborrow {
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        is_mut: bool,
    },
    Collapse(MaybeOldPlace<'tcx>, Vec<MaybeOldPlace<'tcx>>),
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct UnblockEdge<'tcx> {
    pub block: BasicBlock,
    pub edge_type: UnblockEdgeType<'tcx>,
}

impl<'tcx> UnblockEdge<'tcx> {
    pub fn is_mut_reborrow(&self) -> bool {
        match &self.edge_type {
            UnblockEdgeType::Reborrow { is_mut, .. } => *is_mut,
            _ => false,
        }
    }
    pub fn relevant_for_path(&self, path: &[BasicBlock]) -> bool {
        if !path.contains(&self.block) {
            return false;
        }
        let relevant = |place: &MaybeOldPlace<'tcx>| {
            place
                .location()
                .map_or(true, |loc| path.contains(&loc.block))
        };
        match &self.edge_type {
            UnblockEdgeType::Reborrow {
                blocker, blocked, ..
            } => relevant(blocker) && relevant(blocked),
            UnblockEdgeType::Projection(edge) => relevant(&edge.blocked),
            UnblockEdgeType::Abstraction(edge) =>
            /* TODO */
            {
                true
            }
        }
    }

    /// These places must expire to make this edge accessible
    pub fn blocked_by_places(&self, tcx: TyCtxt<'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        match &self.edge_type {
            UnblockEdgeType::Reborrow {
                is_mut,
                blocker,
                blocked,
            } => vec![*blocker],
            UnblockEdgeType::Projection(edge) => edge.blocker_places(tcx),
            UnblockEdgeType::Abstraction(edge) => edge.blocker_places().into_iter().collect(),
        }
    }

    /// This edge must expire for these places to become accessible
    pub fn blocked_places(&self) -> Vec<MaybeOldPlace<'tcx>> {
        match &self.edge_type {
            UnblockEdgeType::Reborrow {
                is_mut,
                blocker,
                blocked,
            } => vec![*blocked],
            UnblockEdgeType::Projection(edge) => vec![edge.blocked],
            UnblockEdgeType::Abstraction(edge) => edge.blocked_places().into_iter().collect(),
        }
    }

    /// This edge must expire to make `place` accessible
    pub fn blocks_place(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.blocked_places().contains(&place)
    }

    /// `place` must expire to make this edge accessible
    pub fn blocked_by_place(&self, tcx: TyCtxt<'tcx>, place: MaybeOldPlace<'tcx>) -> bool {
        self.blocked_by_places(tcx).contains(&place)
    }
}

impl<'a, 'tcx> Analysis<'tcx> for PcsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.fpcs
            .apply_before_statement_effect(&mut state.fpcs, statement, location);
        state.borrows.after.ensure_deref_expansions_to_fpcs(
            self.cgx.rp.tcx(),
            self.cgx.rp.body(),
            &state.fpcs.after,
            location,
        );
        self.borrows
            .apply_before_statement_effect(&mut state.borrows, statement, location);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.fpcs
            .apply_statement_effect(&mut state.fpcs, statement, location);
        state.borrows.after.ensure_deref_expansions_to_fpcs(
            self.cgx.rp.tcx(),
            self.cgx.rp.body(),
            &state.fpcs.after,
            location,
        );
        self.borrows
            .apply_statement_effect(&mut state.borrows, statement, location);
    }
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        self.borrows
            .apply_before_terminator_effect(&mut state.borrows, terminator, location);
        self.fpcs
            .apply_before_terminator_effect(&mut state.fpcs, terminator, location);
    }
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.borrows
            .apply_terminator_effect(&mut state.borrows, terminator, location);
        self.fpcs
            .apply_terminator_effect(&mut state.fpcs, terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}
