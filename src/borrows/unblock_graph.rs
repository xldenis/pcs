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
        unblock_reason::{UnblockReason, UnblockReasons},
    },
    combined_pcs::{ProjectionEdge, RegionEdge, UnblockAction, UnblockEdge, UnblockEdgeType},
    free_pcs::{
        engine::FpcsEngine, CapabilityKind, CapabilityLocal, CapabilitySummary,
        FreePlaceCapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceOrdering, PlaceRepacker},
    visualization::generate_unblock_dot_graph,
};
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

    pub fn filter_for_path(&mut self, path: &[BasicBlock], tcx: TyCtxt<'tcx>) {
        let edges_to_kill = self
            .0
            .iter()
            .cloned()
            .filter(|edge| !edge.relevant_for_path(path))
            .collect::<Vec<_>>();
        for edge in edges_to_kill {
            self.remove_edge_and_trim(&edge);
        }
        let mut blocking_places = self.blocking_places(tcx).clone();
        for place in blocking_places {
            // TODO: This is to handle the case where reborrow assigned to
            // this place is done multiple times along the same path, there
            // may be a more elegant way to handle this
            let blocking_ref_edges = self
                .edges_blocked_by(tcx, place)
                .into_iter()
                .filter(|edge| edge.is_mut_reborrow())
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
                if edge != candidate {
                    self.remove_edge_and_trim(&edge);
                }
            }
        }
    }

    fn remove_edge_and_trim(&mut self, edge: &UnblockEdge<'tcx>) {
        self.0.remove(edge);
        // TODO
        // if self.edges_blocking(edge.blocked).is_empty() {
        //     let edges_to_kill = self
        //         .edges_blocked_by(edge.blocked)
        //         .into_iter()
        //         .cloned()
        //         .collect::<Vec<_>>();
        //     for edge in edges_to_kill {
        //         self.remove_edge_and_trim(&edge.clone());
        //     }
        // }
    }

    /// Edges that require `place` to expire before becoming available
    fn edges_blocked_by(
        &self,
        tcx: TyCtxt<'tcx>,
        place: MaybeOldPlace<'tcx>,
    ) -> Vec<&UnblockEdge<'tcx>> {
        self.0
            .iter()
            .filter(|e| e.blocked_by_place(tcx, place))
            .collect()
    }

    /// To make `place` accessible, these edges must expire
    fn edges_blocking(&self, place: MaybeOldPlace<'tcx>) -> Vec<&UnblockEdge<'tcx>> {
        self.0.iter().filter(|e| e.blocks_place(place)).collect()
    }

    /// All of the places that are blocked by some edge in the graph.
    /// For each place `p` in this set, there exists some place `p'` such that
    /// accessing `p` requires `p'` to expire.
    fn blocked_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.0.iter().flat_map(|e| e.blocked_places()).collect()
    }

    /// All of the places that block some other place in the graph. For each
    /// place `p` in this set, there exists some place `p'` such that accessing
    /// `p'` requires `p` to expire.
    fn blocking_places(&self, tcx: TyCtxt<'tcx>) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.0
            .iter()
            .flat_map(|e| e.blocked_by_places(tcx))
            .collect()
    }

    pub fn actions(self, tcx: TyCtxt<'tcx>) -> Vec<UnblockAction<'tcx>> {
        let mut edges = self.0;
        let mut actions = vec![];

        // There might be duplicates because the same action may be required by
        // two unblocks in the graphs that occur for different reasons down this
        // path. TODO: Confirm that such graphs are actually valid
        let mut push_action = |action| {
            if !actions.contains(&action) {
                actions.push(action);
            }
        };

        while edges.len() > 0 {
            let mut to_keep = edges.clone();

            // A place is a leaf iff no other edge blocks it
            let is_leaf = |node| edges.iter().all(|e| !e.blocks_place(node));

            // A region is a leaf if no edge contains a region blocked by it,
            // and all places blocked by the region are leaves
            let is_leaf_abstraction = |abstraction: &RegionEdge<'tcx>| {
                abstraction
                    .blocker_places
                    .iter()
                    .all(|place| is_leaf(*place))
                    && abstraction.blocker_regions.iter().all(|region_vid| {
                        edges.iter().all(|e| match &e.edge_type {
                            UnblockEdgeType::Region(edge) => edge.region_vid() != *region_vid,
                            _ => true,
                        })
                    })
            };
            for edge in edges.iter() {
                match &edge.edge_type {
                    UnblockEdgeType::Reborrow {
                        is_mut,
                        blocker,
                        blocked,
                    } => {
                        if is_leaf(*blocker) {
                            push_action(UnblockAction::TerminateReborrow {
                                blocked_place: *blocked,
                                assigned_place: *blocker,
                                is_mut: *is_mut,
                            });
                            to_keep.remove(edge);
                        }
                    }
                    UnblockEdgeType::Projection(proj_edge) => {
                        let expansion = proj_edge.blocker_places(tcx);
                        if expansion.iter().all(|p| is_leaf(*p)) {
                            push_action(UnblockAction::Collapse(proj_edge.blocked, expansion));
                            to_keep.remove(edge);
                        }
                    }
                    UnblockEdgeType::Region(region_edge) => {
                        if is_leaf_abstraction(&region_edge) {
                            push_action(UnblockAction::TerminateRegion(
                                region_edge.region_vid(),
                                region_edge.abstraction_type().clone(),
                            ));
                            to_keep.remove(edge);
                        }
                    }
                }
            }
            assert!(
                to_keep.len() < edges.len(),
                "Didn't remove any leaves! {:#?}",
                edges
            );
            edges = to_keep;
        }
        actions
    }

    fn add_dependency(
        &mut self,
        edge_type: UnblockEdgeType<'tcx>,
        block: BasicBlock,
        reason: UnblockReasons<'tcx>,
    ) {
        let existing = self
            .0
            .iter()
            .find(|e| e.block == block && e.edge_type == edge_type);
        if let Some(existing) = existing {
            let mut existing = existing.clone();
            self.0.remove(&existing);
            existing.reason = existing.reason.merge(reason);
            self.0.insert(existing);
        } else {
            self.0.insert(UnblockEdge {
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
        tcx: TyCtxt<'tcx>,
    ) {
        for reborrow in borrows.reborrows_assigned_to(place) {
            self.kill_reborrow(
                reborrow.clone(),
                borrows,
                UnblockReasons::new(UnblockReason::ReborrowAssignedTo(
                    reborrow.clone(),
                    place.clone(),
                )),
                block,
                tcx,
            )
        }
    }

    pub fn kill_place<'a>(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        block: BasicBlock,
        tcx: TyCtxt<'tcx>,
    ) {
        self.unblock_place(
            place,
            borrows,
            block,
            UnblockReasons::new(UnblockReason::KillPlace(place)),
            tcx,
        );
        self.kill_reborrows_assigned_to(place, borrows, block, tcx);
    }

    pub fn unblock_place<'a>(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        block: BasicBlock,
        reason: UnblockReasons<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) {
        for reborrow in borrows.reborrows_blocking(place) {
            self.kill_reborrow(
                reborrow.clone(),
                borrows,
                reason.clone().add(UnblockReason::ReborrowBlocksPlace(
                    reborrow.clone(),
                    place.clone(),
                )),
                block,
                tcx,
            )
        }

        if let Some(expansion) = borrows.deref_expansions.iter().find(|de| de.base == place) {
            self.add_dependency(
                UnblockEdgeType::Projection(ProjectionEdge {
                    blockers: expansion.expansion.clone(),
                    blocked: place,
                }),
                block,
                reason.clone().add(UnblockReason::Projection(place)),
            );
            for place in &expansion.expansion(tcx) {
                self.kill_place(place.clone(), borrows, block, tcx);
            }
        }

        for abstraction in borrows.get_abstractions_blocking(place) {
            self.add_dependency(
                UnblockEdgeType::Region(RegionEdge::new(
                    abstraction.blocked_by_places().into_iter().collect(),
                    borrows
                        .get_abstractions_blocking_region(abstraction.region)
                        .into_iter()
                        .map(|a| a.region)
                        .collect(),
                    abstraction.region,
                    abstraction.abstraction_type.clone(),
                )),
                block,
                reason
                    .clone()
                    .add(UnblockReason::KillAbstraction(abstraction.region)),
            );
        }
    }

    pub fn kill_reborrow<'a>(
        &mut self,
        reborrow: Reborrow<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        reason: UnblockReasons<'tcx>,
        block: BasicBlock,
        tcx: TyCtxt<'tcx>,
    ) {
        self.add_dependency(
            UnblockEdgeType::Reborrow {
                is_mut: reborrow.mutability == Mutability::Mut,
                blocker: reborrow.assigned_place,
                blocked: reborrow.blocked_place,
            },
            block,
            reason
                .clone()
                .add(UnblockReason::KillReborrow(reborrow.clone())),
        );
        self.unblock_place(
            reborrow.assigned_place,
            borrows,
            reborrow.location.block,
            reason.add(UnblockReason::KillReborrowAssignedPlace(
                reborrow.clone(),
                reborrow.assigned_place.clone(),
            )),
            tcx,
        );
        // TODO: confirm right block
    }
}
