// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{cell::Cell, rc::Rc};

use itertools::Itertools;
use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{self, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
    },
    data_structures::fx::FxHashSet,
    dataflow::{Analysis, AnalysisDomain},
    index::{Idx, IndexVec},
    middle::{
        mir::{
            BasicBlock, Body, CallReturnPlaces, Location, PlaceElem, Promoted, Statement,
            Terminator, TerminatorEdges, START_BLOCK,
        },
        ty::{self, TyCtxt, ParamEnv, GenericArgsRef},
    },
};

use crate::{
    borrows::{
        domain::{AbstractionType, MaybeOldPlace},
        engine::BorrowsEngine,
    },
    free_pcs::engine::FpcsEngine,
    rustc_interface,
    utils::PlaceRepacker,
};

use super::domain::PlaceCapabilitySummary;

#[derive(Clone)]

pub struct BodyWithBorrowckFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub location_table: Option<Rc<LocationTable>>,
    pub input_facts: Option<Box<PoloniusInput>>,
    pub output_facts: Option<Rc<PoloniusOutput>>,
}

impl<'tcx> BodyWithBorrowckFacts<'tcx> {
    pub fn monomorphize(
        self,
        tcx: ty::TyCtxt<'tcx>,
        substs: GenericArgsRef<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Self {
        let body = tcx.erase_regions(self.body.clone());
        let monomorphized_body = tcx.instantiate_and_normalize_erasing_regions(
            substs,
            param_env,
            ty::EarlyBinder::bind(body),
        );
        Self {
            body: monomorphized_body,
            promoted: self.promoted,
            borrow_set: self.borrow_set,
            region_inference_context: self.region_inference_context,
            input_facts: self.input_facts,
            location_table: self.location_table,
            output_facts: self.output_facts,
        }
    }
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

#[derive(Debug, Eq, PartialEq)]
pub enum UnblockAction<'tcx> {
    TerminateAbstraction(Location, AbstractionType<'tcx>),
    TerminateReborrow {
        reserve_location: Location,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        is_mut: bool,
    },
    Collapse(MaybeOldPlace<'tcx>, Vec<MaybeOldPlace<'tcx>>),
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
