

use rustc_interface::{
    ast::Mutability,
    data_structures::fx::{FxHashSet},
    dataflow::{JoinSemiLattice},
    middle::mir::{self, BasicBlock, Location},
    middle::ty::{self, TyCtxt},
};
use serde_json::{json, Value};

use crate::{
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceRepacker},
    ReborrowBridge,
};

use super::{
    borrows_graph::{BorrowsEdge, BorrowsGraph, ToBorrowsEdge},
    borrows_visitor::DebugCtx,
    deref_expansion::DerefExpansion,
    domain::{Latest, MaybeOldPlace, Reborrow, RegionProjection},
    path_condition::{PathCondition, PathConditions},
    region_abstraction::RegionAbstraction,
    unblock_graph::UnblockGraph,
};

impl<'mir, 'tcx> JoinSemiLattice for BorrowsState<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        if self.graph.join(&other.graph) {
            changed = true;
        }
        if self.latest.join(&other.latest, self.body) {
            changed = true;
        }
        changed
    }
}

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

#[derive(Clone, Debug)]
pub struct BorrowsState<'mir, 'tcx> {
    body: &'mir mir::Body<'tcx>,
    latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
}

impl<'mir, 'tcx> PartialEq for BorrowsState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph && self.latest == other.latest
    }
}

impl<'mir, 'tcx> Eq for BorrowsState<'mir, 'tcx> {}

fn deref_expansions_should_be_considered_same<'tcx>(
    exp1: &DerefExpansion<'tcx>,
    exp2: &DerefExpansion<'tcx>,
) -> bool {
    match (exp1, exp2) {
        (
            DerefExpansion::OwnedExpansion { base: b1, .. },
            DerefExpansion::OwnedExpansion { base: b2, .. },
        ) => b1 == b2,
        (DerefExpansion::BorrowExpansion(b1), DerefExpansion::BorrowExpansion(b2)) => b1 == b2,
        _ => false,
    }
}

fn subtract_deref_expansions<'tcx>(
    from: &FxHashSet<DerefExpansion<'tcx>>,
    to: &FxHashSet<DerefExpansion<'tcx>>,
) -> FxHashSet<DerefExpansion<'tcx>> {
    from.iter()
        .filter(|f1| {
            to.iter()
                .all(|f2| !deref_expansions_should_be_considered_same(f1, f2))
        })
        .cloned()
        .collect()
}

impl<'mir, 'tcx> BorrowsState<'mir, 'tcx> {
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
        debug_ctx: DebugCtx,
    ) -> bool {
        self.graph.delete_descendants_of(place, repacker, debug_ctx)
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

    pub fn deref_expansions(&self) -> FxHashSet<DerefExpansion<'tcx>> {
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

    // TODO: Remove
    pub fn region_projection_members(&self) -> RegionProjectionMembers<'tcx> {
        self.graph.region_projection_members()
    }

    pub fn reborrows_blocked_by(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<Reborrow<'tcx>> {
        self.graph.reborrows_blocked_by(place)
    }

    pub fn reborrows(&self) -> FxHashSet<Reborrow<'tcx>> {
        self.graph.reborrows()
    }

    pub fn bridge(&self, to: &Self, block: BasicBlock, tcx: TyCtxt<'tcx>) -> ReborrowBridge<'tcx> {
        let repacker = PlaceRepacker::new(self.body, tcx);
        let added_reborrows: FxHashSet<Reborrow<'tcx>> = to
            .reborrows()
            .iter()
            .filter(|rb| !self.has_reborrow_at_location(rb.location))
            .cloned()
            .collect();
        let expands = subtract_deref_expansions(&to.deref_expansions(), &self.deref_expansions());

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows().iter() {
            if !to.has_reborrow_at_location(reborrow.location) {
                ug.kill_reborrow(reborrow, self, block, repacker);
            }
        }

        for exp in subtract_deref_expansions(&self.deref_expansions(), &to.deref_expansions()) {
            ug.unblock_place(exp.base(), self, block, repacker);
        }

        for abstraction in self.region_abstractions().iter() {
            if !to.region_abstractions().contains(&abstraction) {
                ug.kill_abstraction(
                    self,
                    &abstraction.abstraction_type,
                    PlaceRepacker::new(self.body, tcx),
                );
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
    ) -> Vec<RegionAbstraction<'tcx>> {
        self.region_abstractions()
            .iter()
            .filter(|abstraction| abstraction.blocks(place))
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
        ug.unblock_place(
            place.into(),
            self,
            location.block,
            PlaceRepacker::new(body, tcx),
        );
        self.apply_unblock_graph(ug, tcx, DebugCtx::new(location));

        // Originally we may not have been expanded enough
        self.graph
            .ensure_expansion_to_exactly(place.into(), body, tcx, location);
    }

    /// Returns places in the PCS that are reborrowed
    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<Place<'tcx>> {
        self.graph.roots(repacker)
    }

    pub fn kill_reborrows(
        &mut self,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
    ) -> bool {
        self.graph.kill_reborrows(blocked_place, assigned_place)
    }

    pub fn apply_unblock_graph(
        &mut self,
        graph: UnblockGraph<'tcx>,
        tcx: TyCtxt<'tcx>,
        debug_ctx: DebugCtx,
    ) -> bool {
        let mut changed = false;
        for action in graph.actions(tcx) {
            match action {
                crate::combined_pcs::UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    ..
                } => {
                    if self.kill_reborrows(blocked_place, assigned_place) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.graph.delete_descendants_of(
                        place,
                        PlaceRepacker::new(self.body, tcx),
                        debug_ctx,
                    ) {
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

    pub fn reborrows_blocking(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<Reborrow<'tcx>> {
        self.reborrows()
            .iter()
            .filter(|rb| rb.blocked_place == place)
            .cloned()
            .collect()
    }

    pub fn reborrows_assigned_to(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<Reborrow<'tcx>> {
        self.reborrows()
            .iter()
            .filter(|rb| rb.assigned_place == place)
            .cloned()
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

    pub fn region_abstractions(&self) -> FxHashSet<RegionAbstraction<'tcx>> {
        self.graph.region_abstractions()
    }

    pub fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({})
    }

    pub fn new(body: &'mir mir::Body<'tcx>) -> Self {
        Self {
            body,
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
