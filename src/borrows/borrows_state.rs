use rustc_interface::{
    ast::Mutability,
    borrowck::consumers::BorrowIndex,
    data_structures::fx::FxHashSet,
    dataflow::JoinSemiLattice,
    middle::mir::{self, BasicBlock, Location},
    middle::ty::{self, TyCtxt},
};
use serde_json::{json, Value};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker},
    ReborrowBridge,
};

use super::{
    borrows_graph::{BorrowsEdge, BorrowsEdgeKind, BorrowsGraph, Conditioned, ToBorrowsEdge},
    borrows_visitor::DebugCtx,
    deref_expansion::DerefExpansion,
    domain::{Latest, MaybeOldPlace, Reborrow, RegionProjection},
    path_condition::{PathCondition, PathConditions},
    region_abstraction::RegionAbstraction,
    unblock_graph::UnblockGraph,
};

#[derive(Clone, Debug, Hash, PartialEq, Eq, Copy)]
pub enum RegionProjectionMemberDirection {
    PlaceIsRegionInput,
    PlaceIsRegionOutput,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegionProjectionMember<'tcx> {
    pub place: MaybeOldPlace<'tcx>,
    pub projection: RegionProjection<'tcx>,
    pub location: Location,
    pub direction: RegionProjectionMemberDirection,
}

impl<'tcx> RegionProjectionMember<'tcx> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.place.make_place_old(place, latest);
    }

    pub fn projection_index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.projection.index(repacker)
    }

    pub fn new(
        place: MaybeOldPlace<'tcx>,
        projection: RegionProjection<'tcx>,
        location: Location,
        direction: RegionProjectionMemberDirection,
    ) -> Self {
        Self {
            place,
            projection,
            location,
            direction,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionProjectionMembers<'tcx>(pub FxHashSet<RegionProjectionMember<'tcx>>);

impl<'tcx> RegionProjectionMembers<'tcx> {
    pub fn join(&mut self, other: &Self) -> bool {
        let old_size = self.0.len();
        self.0.extend(other.0.iter().cloned());
        self.0.len() != old_size
    }
    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    pub fn insert(&mut self, member: RegionProjectionMember<'tcx>) -> bool {
        self.0.insert(member)
    }

    pub fn iter(&self) -> impl Iterator<Item = &RegionProjectionMember<'tcx>> {
        self.0.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<'tcx> {
    latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
}

fn deref_expansions_should_be_considered_same<'tcx>(
    exp1: &Conditioned<DerefExpansion<'tcx>>,
    exp2: &Conditioned<DerefExpansion<'tcx>>,
) -> bool {
    match (&exp1.value, &exp2.value) {
        (
            DerefExpansion::OwnedExpansion { base: b1, .. },
            DerefExpansion::OwnedExpansion { base: b2, .. },
        ) => b1 == b2,
        (DerefExpansion::BorrowExpansion(b1), DerefExpansion::BorrowExpansion(b2)) => b1 == b2,
        _ => false,
    }
}

fn subtract_deref_expansions<'tcx>(
    from: &FxHashSet<Conditioned<DerefExpansion<'tcx>>>,
    to: &FxHashSet<Conditioned<DerefExpansion<'tcx>>>,
) -> FxHashSet<Conditioned<DerefExpansion<'tcx>>> {
    from.iter()
        .filter(|f1| {
            to.iter()
                .all(|f2| !deref_expansions_should_be_considered_same(f1, f2))
        })
        .cloned()
        .collect()
}

impl<'tcx> BorrowsState<'tcx> {
    pub fn join<'mir>(&mut self, other: &Self, body: &'mir mir::Body<'tcx>) -> bool {
        let mut changed = false;
        if self.graph.join(&other.graph) {
            changed = true;
        }
        if self.latest.join(&other.latest, body) {
            changed = true;
        }
        changed
    }

    pub fn remove_edge_and_set_latest(
        &mut self,
        edge: &BorrowsEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        for place in edge.blocked_places() {
            match place {
                MaybeOldPlace::Current { place } => self.set_latest(place, location),
                _ => {}
            }
        }
        self.graph.remove(edge, DebugCtx::new(location))
    }

    pub fn reborrow_edges_reserved_at(
        &self,
        location: Location,
    ) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.graph
            .edges()
            .filter_map(|edge| match &edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow)
                    if reborrow.reservation_location() == location =>
                {
                    Some(Conditioned {
                        conditions: edge.conditions().clone(),
                        value: reborrow.clone(),
                    })
                }
                _ => None,
            })
            .collect()
    }

    pub fn minimize(&mut self, repacker: PlaceRepacker<'_, 'tcx>, location: Location) {
        loop {
            let to_remove = self
                .graph
                .edges()
                .filter(|edge| {
                    let is_old_unblocked = edge
                        .blocked_by_places(repacker)
                        .iter()
                        .all(|p| p.is_old() && !self.graph.has_edge_blocking(p));
                    is_old_unblocked
                        || match &edge.kind() {
                            BorrowsEdgeKind::DerefExpansion(de) => {
                                !de.is_owned_expansion()
                                    && de
                                        .expansion(repacker)
                                        .into_iter()
                                        .all(|p| !self.graph.has_edge_blocking(&p.into()))
                            }
                            _ => false,
                        }
                })
                .cloned()
                .collect::<Vec<_>>();
            if to_remove.is_empty() {
                break;
            }
            for edge in to_remove {
                self.remove_edge_and_set_latest(&edge, repacker, location);
            }
        }
    }

    pub fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.graph.add_path_condition(pc)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.graph.filter_for_path(path);
    }

    pub fn delete_descendants_of(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let mut changed = false;
        let edges = self.edges_blocking(place).cloned().collect::<Vec<_>>();
        for edge in edges {
            changed = true;
            self.remove_edge_and_set_latest(&edge, repacker, location);
        }
        changed
    }

    pub fn edges_blocking(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.graph.edges_blocking(place)
    }

    pub fn graph_edges(&self) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.graph.edges()
    }

    pub fn deref_expansions(&self) -> FxHashSet<Conditioned<DerefExpansion<'tcx>>> {
        self.graph.deref_expansions()
    }

    pub fn move_region_projection_member_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.graph.move_region_projection_member_projections(
            old_projection_place,
            new_projection_place,
            repacker,
        );
    }

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        self.graph
            .move_reborrows(orig_assigned_place, new_assigned_place);
    }

    pub fn reborrows_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.graph.reborrows_blocked_by(place)
    }

    pub fn reborrows(&self) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.graph.reborrows()
    }

    pub fn bridge(&self, to: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> ReborrowBridge<'tcx> {
        let added_reborrows: FxHashSet<Conditioned<Reborrow<'tcx>>> = to
            .reborrows()
            .into_iter()
            .filter(|rb| !self.has_reborrow_at_location(rb.value.reservation_location()))
            .collect();
        let expands = subtract_deref_expansions(&to.deref_expansions(), &self.deref_expansions());

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows() {
            if !to.has_reborrow_at_location(reborrow.value.reservation_location()) {
                ug.kill_reborrow(reborrow, self, repacker);
            }
        }

        for exp in subtract_deref_expansions(&self.deref_expansions(), &to.deref_expansions()) {
            ug.unblock_place(exp.value.base(), self, repacker);
        }

        for abstraction in self.region_abstractions() {
            if !to.region_abstractions().contains(&abstraction) {
                ug.kill_abstraction(self, abstraction, repacker);
            }
        }

        ReborrowBridge {
            added_reborrows,
            expands,
            ug,
        }
    }

    pub fn ensure_deref_expansions_to_fpcs(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        summary: &CapabilitySummary<'tcx>,
        location: Location,
    ) {
        for c in (*summary).iter() {
            match c {
                CapabilityLocal::Allocated(projections) => {
                    for (place, kind) in (*projections).iter() {
                        match kind {
                            CapabilityKind::Exclusive => {
                                if place.is_ref(body, tcx) {
                                    self.graph.ensure_deref_expansion_to_at_least(
                                        place.project_deref(PlaceRepacker::new(body, tcx)),
                                        body,
                                        tcx,
                                        location,
                                    );
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub fn get_abstractions_blocking(
        &self,
        place: &MaybeOldPlace<'tcx>,
    ) -> Vec<Conditioned<RegionAbstraction<'tcx>>> {
        self.region_abstractions()
            .iter()
            .filter(|abstraction| abstraction.value.blocks(place))
            .cloned()
            .collect()
    }

    pub fn ensure_expansion_to_exactly(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: Place<'tcx>,
        location: Location,
    ) {
        let mut ug = UnblockGraph::new();
        let repacker = PlaceRepacker::new(body, tcx);
        ug.unblock_place(place.into(), self, repacker);
        self.apply_unblock_graph(ug, repacker, location);

        // Originally we may not have been expanded enough
        self.graph
            .ensure_deref_expansion_to_at_least(place.into(), body, tcx, location);
    }

    /// Returns places in the PCS that are reborrowed
    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<Place<'tcx>> {
        self.graph.roots(repacker)
    }

    // TODO: THIS SHOULD BE PATH SENSITIVE!
    pub fn kill_reborrows(
        &mut self,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let edges_to_remove = self
            .graph
            .edges()
            .filter(|edge| {
                if let BorrowsEdgeKind::Reborrow(reborrow) = &edge.kind() {
                    reborrow.blocked_place == blocked_place
                        && reborrow.assigned_place == assigned_place
                } else {
                    false
                }
            })
            .cloned()
            .collect::<Vec<_>>();
        if edges_to_remove.is_empty() {
            return false;
        }
        for edge in edges_to_remove {
            self.remove_edge_and_set_latest(&edge, repacker, location);
        }
        true
    }

    pub fn apply_unblock_graph(
        &mut self,
        graph: UnblockGraph<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let mut changed = false;
        for action in graph.actions(repacker) {
            match action {
                crate::combined_pcs::UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    ..
                } => {
                    if self.kill_reborrows(blocked_place, assigned_place, repacker, location) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.delete_descendants_of(place, repacker, location) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::TerminateAbstraction(location, _call) => {
                    self.graph.remove_abstraction_at(location);
                }
            }
        }
        changed
    }

    pub fn set_latest(&mut self, place: Place<'tcx>, location: Location) {
        self.latest.insert(place, location);
    }

    pub fn get_latest(&self, place: &Place<'tcx>) -> Location {
        self.latest.get(place)
    }

    pub fn reborrows_blocking(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.reborrows()
            .into_iter()
            .filter(|rb| rb.value.blocked_place == place)
            .collect()
    }

    pub fn reborrows_assigned_to(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<Reborrow<'tcx>>> {
        self.reborrows()
            .into_iter()
            .filter(|rb| rb.value.assigned_place == place)
            .collect()
    }

    pub fn add_region_projection_member(&mut self, member: RegionProjectionMember<'tcx>) {
        self.graph.insert(
            member
                .clone()
                .to_borrows_edge(PathConditions::new(member.location.block)),
        );
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: ty::Region<'tcx>,
    ) {
        self.graph
            .add_reborrow(blocked_place, assigned_place, mutability, location, region);
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.graph.has_reborrow_at_location(location)
    }

    pub fn region_abstractions(&self) -> FxHashSet<Conditioned<RegionAbstraction<'tcx>>> {
        self.graph.region_abstractions()
    }

    pub fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({})
    }

    pub fn new() -> Self {
        Self {
            latest: Latest::new(),
            graph: BorrowsGraph::new(),
        }
    }

    pub fn add_region_abstraction(
        &mut self,
        abstraction: RegionAbstraction<'tcx>,
        block: BasicBlock,
    ) {
        self.graph
            .insert(abstraction.to_borrows_edge(PathConditions::new(block)));
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        _repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) {
        self.graph.make_place_old(place, &self.latest, debug_ctx);
    }
}
