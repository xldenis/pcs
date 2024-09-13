use std::collections::HashSet;

use rustc_interface::{
    ast::Mutability,
    middle::{
        mir::{BasicBlock, Location},
        ty::TyCtxt,
    },
};

use crate::{
    borrows::{
        borrows_state::BorrowsState,
        domain::{MaybeOldPlace, Reborrow},
    },
    combined_pcs::{ProjectionEdge, UnblockAction},
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
    visualization::generate_unblock_dot_graph,
};

use super::{
    borrows_graph::{BorrowsEdge, BorrowsEdgeKind, Conditioned},
    domain::{AbstractionType, ReborrowBlockedPlace},
    region_abstraction::RegionAbstraction,
};

type UnblockEdge<'tcx> = BorrowsEdge<'tcx>;
type UnblockEdgeType<'tcx> = BorrowsEdgeKind<'tcx>;
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

    pub fn for_place(
        place: ReborrowBlockedPlace<'tcx>,
        state: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        ug.unblock_place(place, state, repacker);
        ug
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.0.retain(|edge| edge.valid_for_path(path));
    }

    pub fn actions(self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<UnblockAction<'tcx>> {
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
            let is_leaf_abstraction = |abstraction: &AbstractionType<'tcx>| {
                abstraction
                    .blocker_places()
                    .iter()
                    .all(|place| is_leaf(*place))
                // && abstraction.blocker_regions.iter().all(|region_vid| {
                //     edges.iter().all(|e| match &e.edge_type {
                //         UnblockEdgeType::Abstraction(edge) => {
                //             edge.location() != abstraction.location()
                //         }
                //         _ => true,
                //     })
                // })
            };
            for edge in edges.iter() {
                match edge.kind() {
                    UnblockEdgeType::Reborrow(reborrow) => {
                        if is_leaf(reborrow.assigned_place) {
                            push_action(UnblockAction::TerminateReborrow {
                                blocked_place: reborrow.blocked_place,
                                assigned_place: reborrow.assigned_place,
                                reserve_location: reborrow.reserve_location(),
                                is_mut: reborrow.mutability == Mutability::Mut,
                            });
                            to_keep.remove(edge);
                        }
                    }
                    UnblockEdgeType::DerefExpansion(deref_edge) => {
                        let expansion = deref_edge.expansion(repacker);
                        if expansion.iter().all(|p| is_leaf(*p)) {
                            push_action(UnblockAction::Collapse(deref_edge.base(), expansion));
                            to_keep.remove(edge);
                        }
                    }
                    UnblockEdgeType::RegionAbstraction(abstraction_edge) => {
                        if is_leaf_abstraction(&abstraction_edge.abstraction_type) {
                            push_action(UnblockAction::TerminateAbstraction(
                                abstraction_edge.location(),
                                abstraction_edge.abstraction_type.clone(),
                            ));
                            to_keep.remove(edge);
                        }
                    }
                    _ => {}
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

    fn add_dependency(&mut self, unblock_edge: UnblockEdge<'tcx>) {
        self.0.insert(unblock_edge);
    }

    pub fn kill_abstraction(
        &mut self,
        borrows: &BorrowsState<'tcx>,
        abstraction: Conditioned<RegionAbstraction<'tcx>>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for place in &abstraction.value.blocks_places() {
            match place {
                MaybeOldPlace::OldPlace(p) => {
                    self.trim_old_leaves_from(borrows, p.clone(), repacker)
                }
                _ => {}
            }
        }
        self.add_dependency(abstraction.to_borrows_edge());
    }

    pub fn unblock_place(
        &mut self,
        place: ReborrowBlockedPlace<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for edge in borrows.edges_blocking(place) {
            match edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => self.kill_reborrow(
                    Conditioned::new(reborrow.clone(), edge.conditions().clone()),
                    borrows,
                    repacker,
                ),
                BorrowsEdgeKind::DerefExpansion(expansion) => {
                    self.add_dependency(edge.clone());
                    for place in expansion.expansion(repacker) {
                        self.unblock_place(place.into(), borrows, repacker);
                    }
                }
                BorrowsEdgeKind::RegionAbstraction(abstraction) => {
                    for place in abstraction.abstraction_type.blocker_places() {
                        self.unblock_place(place.into(), borrows, repacker);
                    }
                    self.add_dependency(edge.clone());
                }
                BorrowsEdgeKind::RegionProjectionMember(_) => {
                    // TODO
                }
            }
        }
    }

    pub fn kill_reborrows_reserved_at(
        &mut self,
        location: Location,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for edge in borrows.reborrow_edges_reserved_at(location) {
            self.unblock_place(edge.value.assigned_place.into(), borrows, repacker);
            self.add_dependency(edge.to_borrows_edge());
        }
    }

    pub fn kill_reborrow(
        &mut self,
        reborrow: Conditioned<Reborrow<'tcx>>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.unblock_place(reborrow.value.assigned_place.into(), borrows, repacker);
        self.add_dependency(reborrow.to_borrows_edge());
    }

    pub fn trim_old_leaves_from(
        &mut self,
        borrows: &BorrowsState<'tcx>,
        place: PlaceSnapshot<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for reborrow in borrows.reborrows_blocked_by(MaybeOldPlace::OldPlace(place)) {
            match reborrow.value.blocked_place {
                ReborrowBlockedPlace::Local(MaybeOldPlace::OldPlace(p)) => {
                    self.trim_old_leaves_from(borrows, p.clone(), repacker)
                }
                _ => {}
            }
            self.kill_reborrow(reborrow, borrows, repacker);
        }
    }
}
