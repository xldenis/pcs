use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::{
        fx::{FxHashMap, FxHashSet},
        graph::dominators::Dominators,
    },
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Local, Location, VarDebugInfo, PlaceElem},
    middle::ty::{self, RegionVid, TyCtxt},
};
use serde_json::{json, Value};

use crate::{
    combined_pcs::PlaceCapabilitySummary,
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary,
        FreePlaceCapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::{
    borrows_visitor::DebugCtx, deref_expansion::DerefExpansion, deref_expansions::{self, DerefExpansions}, domain::{
        AbstractionBlockEdge, AbstractionTarget, AbstractionType, Borrow, Latest, MaybeOldPlace, Reborrow, RegionProjection
    }, reborrowing_dag::ReborrowingDag, unblock_graph::UnblockGraph
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct RegionAbstraction<'tcx> {
    pub abstraction_type: AbstractionType<'tcx>,
}

impl<'tcx> RegionAbstraction<'tcx> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.abstraction_type.make_place_old(place, latest);
    }

    pub fn new(abstraction_type: AbstractionType<'tcx>) -> Self {
        Self { abstraction_type }
    }

    pub fn location(&self) -> Location {
        self.abstraction_type.location()
    }

    pub fn inputs(&self) -> Vec<&AbstractionTarget<'tcx>> {
        self.abstraction_type.inputs()
    }

    pub fn outputs(&self) -> Vec<&AbstractionTarget<'tcx>> {
        self.abstraction_type.outputs()
    }

    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.abstraction_type.blocks(place)
    }

    pub fn blocks_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocks_places()
    }

    pub fn blocked_by_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocker_places()
    }

    pub fn edges(&self) -> impl Iterator<Item = &AbstractionBlockEdge<'tcx>> {
        match &self.abstraction_type {
            AbstractionType::FunctionCall { edges, .. } => edges.iter().map(|(_, edge)| edge),
        }
    }
}

#[derive(Clone, Debug)]
pub struct RegionAbstractions<'tcx>(pub Vec<RegionAbstraction<'tcx>>);

impl<'tcx> RegionAbstractions<'tcx> {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn contains(&self, abstraction: &RegionAbstraction<'tcx>) -> bool {
        self.0.contains(abstraction)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.0
            .retain(|abstraction| path.contains(&abstraction.location().block));
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        for abstraction in &mut self.0 {
            abstraction.make_place_old(place, latest);
        }
    }

    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|abstraction| abstraction.blocks(place))
    }

    pub fn insert(&mut self, abstraction: RegionAbstraction<'tcx>) -> bool {
        if !self.0.contains(&abstraction) {
            self.0.push(abstraction);
            true
        } else {
            false
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &RegionAbstraction<'tcx>> {
        self.0.iter()
    }
    pub fn delete_region(&mut self, location: Location) {
        self.0
            .retain(|abstraction| abstraction.location() != location);
    }
}
