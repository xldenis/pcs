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
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Promoted, Rvalue,
            Statement, StatementKind, Terminator, TerminatorEdges, RETURN_PLACE, START_BLOCK,
        },
        ty::TyCtxt,
    },
};

use crate::{
    borrows::{
        borrows_state::BorrowsState,
        deref_expansions::DerefExpansions,
        domain::{MaybeOldPlace, Reborrow},
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
pub enum UnblockEdgeType {
    Reborrow { is_mut: bool },
    Projection(usize),
}

impl UnblockEdgeType {
    pub fn expect_projection(&self) -> usize {
        if let UnblockEdgeType::Projection(idx) = self {
            *idx
        } else {
            panic!("Expected projection edge type, got {self:?}");
        }
    }
}

#[derive(Debug)]
pub enum UnblockAction<'tcx> {
    TerminateReborrow {
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        is_mut: bool,
    },
    Collapse(MaybeOldPlace<'tcx>, Vec<MaybeOldPlace<'tcx>>),
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct UnblockEdge<'tcx> {
    pub blocked: MaybeOldPlace<'tcx>,
    pub blocker: MaybeOldPlace<'tcx>,
    pub block: BasicBlock,
    pub edge_type: UnblockEdgeType,
    pub reason: String,
}

impl<'tcx> UnblockEdge<'tcx> {
    fn expect_projection(&self) -> usize {
        self.edge_type.expect_projection()
    }
}

#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx>(HashSet<UnblockEdge<'tcx>>);

impl<'tcx> UnblockGraph<'tcx> {
    pub fn edges(&self) -> impl Iterator<Item = &UnblockEdge<'tcx>> {
        self.0.iter()
    }
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        let dot_graph = generate_unblock_dot_graph(&repacker, self).unwrap();
        serde_json::json!({
            "empty": self.is_empty(),
            "dot_graph": dot_graph
        })
    }
    pub fn new() -> Self {
        Self(HashSet::new())
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        let edges_to_kill = self
            .0
            .iter()
            .cloned()
            .filter(|edge| {
                !path.contains(&edge.block)
                    || edge
                        .blocked
                        .location()
                        .map_or(false, |loc| !path.contains(&loc.block))
                    || edge
                        .blocker
                        .location()
                        .map_or(false, |loc| !path.contains(&loc.block))
            })
            .collect::<Vec<_>>();
        for edge in edges_to_kill {
            self.remove_edge_and_trim(&edge);
        }
        let mut blocking_places = self.blocking_places().clone();
        for place in blocking_places {
            let blocking_ref_edges = self
                .edges_blocked_by(place)
                .into_iter()
                .filter(|e| e.edge_type == UnblockEdgeType::Reborrow { is_mut: true })
                .cloned()
                .collect::<Vec<_>>();
            if blocking_ref_edges.len() < 2 {
                continue;
            }
            let mut candidate = blocking_ref_edges[0].clone();
            for edge in &blocking_ref_edges[1..] {
                if path.iter().position(|b| b == &edge.block)
                    > path.iter().position(|b| b == &candidate.block)
                {
                    candidate = edge.clone();
                }
            }
            for edge in blocking_ref_edges {
                eprintln!("Checking edge: {:?}", edge);
                if edge != candidate {
                    eprintln!("Killing edge: {:?}", edge);
                    self.remove_edge_and_trim(&edge);
                }
            }
        }
    }

    fn remove_edge_and_trim(&mut self, edge: &UnblockEdge<'tcx>) {
        self.0.remove(edge);
        if self.edges_blocking(edge.blocked).is_empty() {
            let edges_to_kill = self
                .edges_blocked_by(edge.blocked)
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            for edge in edges_to_kill {
                self.remove_edge_and_trim(&edge.clone());
            }
        }
    }

    fn edges_blocked_by(&self, place: MaybeOldPlace<'tcx>) -> Vec<&UnblockEdge<'tcx>> {
        self.0.iter().filter(|e| e.blocker == place).collect()
    }

    fn edges_blocking(&self, place: MaybeOldPlace<'tcx>) -> Vec<&UnblockEdge<'tcx>> {
        self.0.iter().filter(|e| e.blocked == place).collect()
    }

    fn blocked_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.0.iter().map(|e| e.blocked).collect()
    }
    fn blocking_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.0.iter().map(|e| e.blocker).collect()
    }

    pub fn actions(self) -> Vec<UnblockAction<'tcx>> {
        let mut edges = self.0;
        let mut actions = vec![];
        while edges.len() > 0 {
            let mut to_keep = edges.clone();
            let is_leaf = |node| edges.iter().all(|e| e.blocked != node);
            for edge in edges.iter() {
                match edge.edge_type {
                    UnblockEdgeType::Reborrow { is_mut } => {
                        if is_leaf(edge.blocker) {
                            actions.push(UnblockAction::TerminateReborrow {
                                blocked_place: edge.blocked,
                                assigned_place: edge.blocker,
                                is_mut,
                            });
                            to_keep.remove(edge);
                        }
                    }
                    _ => {}
                }
            }
            for edge in edges.iter() {
                match edge.edge_type {
                    UnblockEdgeType::Projection(idx) => {
                        let all_projection_edges = edges
                            .iter()
                            .filter(|e| e.blocked == edge.blocked)
                            .collect::<Vec<_>>();
                        if all_projection_edges.iter().all(|e| is_leaf(e.blocker)) {
                            actions.push(UnblockAction::Collapse(
                                edge.blocked,
                                all_projection_edges
                                    .iter()
                                    .sorted_by_key(|e| e.expect_projection())
                                    .map(|e| e.blocker)
                                    .collect(),
                            ));
                            for edge in all_projection_edges {
                                to_keep.remove(&edge);
                            }
                            break; // If we were to continue we may see the same node to collapse again,
                                   // we can make more progress next iteration anyways
                        }
                    }
                    _ => {}
                }
            }
            assert!(
                to_keep.len() < edges.len(),
                "Didn't remove any leaves! {:?}",
                edges
            );
            edges = to_keep;
        }
        actions
    }

    fn add_dependency(
        &mut self,
        blocked: MaybeOldPlace<'tcx>,
        blocker: MaybeOldPlace<'tcx>,
        edge_type: UnblockEdgeType,
        block: BasicBlock,
        reason: String,
    ) {
        let existing = self.0.iter().find(|e| {
            e.blocked == blocked
                && e.blocker == blocker
                && e.block == block
                && e.edge_type == edge_type
        });
        if let Some(existing) = existing {
            if existing.reason.contains(&reason) {
                return;
            }
            let mut existing = existing.clone();
            self.0.remove(&existing);
            existing.reason = format!("{}, and {}", existing.reason, reason);
            self.0.insert(existing);
        } else {
            self.0.insert(UnblockEdge {
                blocked,
                blocker,
                edge_type,
                block,
                reason,
            });
        }
    }

    pub fn kill_reborrows_assigned_to<'a>(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        block: BasicBlock,
    ) {
        for reborrow in borrows.reborrows_assigned_to(place) {
            self.kill_reborrow(
                reborrow.clone(),
                borrows,
                format!("it is assigned to {place:?}"),
            )
        }
    }

    pub fn kill_place<'a>(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        block: BasicBlock,
    ) {
        self.unblock_place(place, borrows, block);
        self.kill_reborrows_assigned_to(place, borrows, block);
    }

    pub fn unblock_place<'a>(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        block: BasicBlock,
    ) {
        for reborrow in borrows.reborrows_blocking(place) {
            self.kill_reborrow(reborrow.clone(), borrows, format!("it blocks {place:?}"))
        }
        for (idx, child_place) in borrows
            .deref_expansions
            .get(place)
            .unwrap_or_default()
            .into_iter()
            .enumerate()
        {
            let child_place = MaybeOldPlace::new(child_place, place.location());
            self.add_dependency(
                place,
                child_place,
                UnblockEdgeType::Projection(idx),
                block,
                format!("Child of {place:?}"),
            );
            self.kill_place(child_place, borrows, block);
        }
    }

    fn places_blocking_collapse(
        place: MaybeOldPlace<'tcx>,
        state: &DerefExpansions<'tcx>,
    ) -> Vec<Place<'tcx>> {
        state.get(place).unwrap_or_default()
    }

    pub fn kill_reborrow<'a>(
        &mut self,
        reborrow: Reborrow<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        reason: String,
    ) {
        self.add_dependency(
            reborrow.blocked_place,
            reborrow.assigned_place,
            UnblockEdgeType::Reborrow {
                is_mut: reborrow.mutability == Mutability::Mut,
            },
            reborrow.location.block, // TODO: Confirm this is the right block to use
            format!("Kill reborrow because {}", reason),
        );
        self.unblock_place(reborrow.assigned_place, borrows, reborrow.location.block);
        // TODO: confirm right block
    }
}

impl<'a, 'tcx> Analysis<'tcx> for PcsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        // match &statement.kind {
        //     StatementKind::Assign(box (place, Rvalue::Use(operand))) if let Some(place) = operand.place() => {
        //         if let Some(place) = state.borrows.after.reference_targeting_place(place.into(), self.cgx.mir.borrow_set.as_ref(), &self.cgx.mir.body) {
        //             if let CapabilityLocal::Allocated(cap) = &mut state.fpcs.after[place.local] {
        //                 let related = cap.find_all_related(place, Some(crate::utils::PlaceOrdering::Suffix));
        //                 cap.collapse(related.get_from(), place, self.cgx.rp);
        //             }
        //         }
        //     }
        //     _ => {}
        // }
        self.borrows
            .apply_before_statement_effect(&mut state.borrows, statement, location);
        self.fpcs
            .apply_before_statement_effect(&mut state.fpcs, statement, location);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.borrows
            .apply_statement_effect(&mut state.borrows, statement, location);
        self.fpcs
            .apply_statement_effect(&mut state.fpcs, statement, location);
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
