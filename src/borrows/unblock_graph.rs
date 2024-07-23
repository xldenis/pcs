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
    }, combined_pcs::{UnblockAction, UnblockEdge, UnblockEdgeType}, free_pcs::{
        engine::FpcsEngine, CapabilityKind, CapabilityLocal, CapabilitySummary,
        FreePlaceCapabilitySummary,
    }, rustc_interface, utils::{Place, PlaceOrdering, PlaceRepacker}, visualization::generate_unblock_dot_graph
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
                if edge != candidate {
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
                            .filter(|e| e.edge_type.is_projection() && e.blocked == edge.blocked)
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
        reason: UnblockReasons<'tcx>,
    ) {
        let existing = self.0.iter().find(|e| {
            e.blocked == blocked
                && e.blocker == blocker
                && e.block == block
                && e.edge_type == edge_type
        });
        if let Some(existing) = existing {
            let mut existing = existing.clone();
            self.0.remove(&existing);
            existing.reason = existing.reason.merge(reason);
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
                tcx,
            )
        }
        for (idx, child_place) in borrows
            .deref_expansions
            .get(place, tcx)
            .unwrap_or_default()
            .into_iter()
            .enumerate()
        {
            self.add_dependency(
                place,
                child_place,
                UnblockEdgeType::Projection(idx),
                block,
                reason
                    .clone()
                    .add(UnblockReason::ChildOfPlace(child_place, place)),
            );
            self.kill_place(child_place, borrows, block, tcx);
        }
    }

    // fn places_blocking_collapse(
    //     place: MaybeOldPlace<'tcx>,
    //     state: &DerefExpansions<'tcx>,
    // ) -> Vec<Place<'tcx>> {
    //     state.get(place).unwrap_or_default()
    // }

    pub fn kill_reborrow<'a>(
        &mut self,
        reborrow: Reborrow<'tcx>,
        borrows: &BorrowsState<'a, 'tcx>,
        reason: UnblockReasons<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) {
        self.add_dependency(
            reborrow.blocked_place,
            reborrow.assigned_place,
            UnblockEdgeType::Reborrow {
                is_mut: reborrow.mutability == Mutability::Mut,
            },
            reborrow.location.block, // TODO: Confirm this is the right block to use
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
