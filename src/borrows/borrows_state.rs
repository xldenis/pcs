use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Local, Location, PlaceElem, VarDebugInfo},
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
    borrows_visitor::DebugCtx,
    deref_expansion::DerefExpansion,
    deref_expansions::{self, DerefExpansions},
    domain::{Borrow, Latest, MaybeOldPlace, Reborrow, RegionProjection},
    path_condition::{PathCondition, PathConditions},
    reborrowing_dag::ReborrowingDag,
    region_abstraction::{RegionAbstraction, RegionAbstractions},
    unblock_graph::UnblockGraph,
};

impl<'mir, 'tcx> JoinSemiLattice for BorrowsState<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for region_abstraction in other.region_abstractions.iter() {
            if self.region_abstractions.insert(region_abstraction.clone()) {
                changed = true;
            }
        }
        for reborrow in other.reborrows.iter() {
            if self.reborrows.insert(reborrow.clone()) {
                changed = true;
            }
        }
        if self.deref_expansions.join(&other.deref_expansions) {
            changed = true;
        }
        if self.latest.join(&other.latest, self.body) {
            changed = true;
        }
        if self
            .region_projection_members
            .join(&other.region_projection_members)
        {
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
pub struct RegionProjectionMembers<'tcx>(FxHashSet<RegionProjectionMember<'tcx>>);

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

    pub fn move_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        eprintln!(
            "Moving projections from {:?} to {:?}",
            old_projection_place, new_projection_place
        );
        let new_data = self
            .0
            .clone()
            .into_iter()
            .map(|mut member| {
                if member.projection.place == old_projection_place {
                    let idx = member.projection_index(repacker);
                    member.projection = new_projection_place.region_projection(idx, repacker);
                }
                member
            })
            .collect();
        self.0 = new_data;
    }
}

#[derive(Clone, Debug)]
pub struct BorrowsState<'mir, 'tcx> {
    body: &'mir mir::Body<'tcx>,
    latest: Latest<'tcx>,
    pub reborrows: ReborrowingDag<'tcx>,
    pub region_abstractions: RegionAbstractions<'tcx>,
    pub deref_expansions: DerefExpansions<'tcx>,
    pub region_projection_members: RegionProjectionMembers<'tcx>,
}

impl<'mir, 'tcx> PartialEq for BorrowsState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.reborrows == other.reborrows
            && self.deref_expansions == other.deref_expansions
            && self.latest == other.latest
            && self.region_projection_members == other.region_projection_members
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
    from: &DerefExpansions<'tcx>,
    to: &DerefExpansions<'tcx>,
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
        self.reborrows.add_path_condition(pc)
    }
    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.reborrows.filter_for_path(path);
        self.deref_expansions.filter_for_path(path);
        self.region_abstractions.filter_for_path(path);
    }
    pub fn bridge(&self, to: &Self, block: BasicBlock, tcx: TyCtxt<'tcx>) -> ReborrowBridge<'tcx> {
        let repacker = PlaceRepacker::new(self.body, tcx);
        let added_reborrows: FxHashSet<Reborrow<'tcx>> = to
            .reborrows()
            .iter()
            .filter(|rb| !self.has_reborrow_at_location(rb.location))
            .cloned()
            .collect();
        let expands = subtract_deref_expansions(&to.deref_expansions, &self.deref_expansions);

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows().iter() {
            if !to.has_reborrow_at_location(reborrow.location) {
                ug.kill_reborrow(reborrow, self, block, repacker);
            }
        }

        for exp in subtract_deref_expansions(&self.deref_expansions, &to.deref_expansions) {
            ug.unblock_place(exp.base(), self, block, repacker);
        }

        for abstraction in self.region_abstractions.iter() {
            if !to.region_abstractions.contains(&abstraction) {
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
                                    self.deref_expansions.ensure_deref_expansion_to_at_least(
                                        &MaybeOldPlace::Current {
                                            place: place
                                                .project_deref(PlaceRepacker::new(body, tcx)),
                                        },
                                        body,
                                        tcx,
                                        location,
                                    );
                                } else {
                                    let mut ug = UnblockGraph::new();
                                    for deref_expansion in self
                                        .deref_expansions
                                        .descendants_of(MaybeOldPlace::Current { place: *place })
                                    {
                                        ug.kill_place(
                                            deref_expansion.base(),
                                            self,
                                            location.block,
                                            PlaceRepacker::new(body, tcx),
                                        );
                                    }
                                    self.apply_unblock_graph(ug, tcx);
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
    ) -> Vec<&RegionAbstraction<'tcx>> {
        self.region_abstractions
            .iter()
            .filter(|abstraction| abstraction.blocks(place))
            .collect()
    }

    pub fn ensure_expansion_to_exactly(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: MaybeOldPlace<'tcx>,
        location: Location,
    ) {
        let mut ug = UnblockGraph::new();
        ug.unblock_place(place, self, location.block, PlaceRepacker::new(body, tcx));
        self.apply_unblock_graph(ug, tcx);

        // Originally we may not have been expanded enough
        self.deref_expansions
            .ensure_expansion_to_exactly(place, body, tcx, location);

        match place.place().last_projection() {
            Some((ref_place, PlaceElem::Deref)) => {}
            _ => {}
        }
    }

    pub fn roots_of(
        &self,
        place: &MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        let mut result = FxHashSet::default();
        for place in self.reborrows.get_places_blocking(place) {
            result.extend(self.roots_of(&place, repacker));
        }
        for place in self.deref_expansions.get_parents(place, repacker) {
            result.extend(self.roots_of(&place, repacker));
        }
        if result.is_empty() {
            result.insert(place.clone());
        }
        result
    }

    pub fn is_leaf(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        !self.region_abstractions.blocks(place)
            && self.reborrows.get_places_blocking(place).is_empty()
            && !self.deref_expansions.contains_expansion_from(place)
    }

    /// Returns places in the PCS that are reborrowed
    pub fn reborrow_roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<Place<'tcx>> {
        self.reborrows
            .roots()
            .into_iter()
            .flat_map(|place| self.roots_of(&place, repacker))
            .flat_map(|place| match place {
                MaybeOldPlace::Current { place } => Some(place),
                MaybeOldPlace::OldPlace(_) => None,
            })
            .collect()
    }

    pub fn apply_unblock_graph(&mut self, graph: UnblockGraph<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        let mut changed = false;
        for action in graph.actions(tcx) {
            match action {
                crate::combined_pcs::UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    ..
                } => {
                    if self.reborrows.kill_reborrows(blocked_place, assigned_place) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.deref_expansions.delete_descendants_of(
                        place,
                        PlaceRepacker::new(self.body, tcx),
                        None,
                    ) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::TerminateAbstraction(location, call) => {
                    self.region_abstractions.delete_region(location);
                }
            }
        }
        changed
    }

    pub fn reborrows(&self) -> &ReborrowingDag<'tcx> {
        &self.reborrows
    }

    pub fn set_latest(&mut self, place: Place<'tcx>, location: Location) {
        self.latest.insert(place, location);
    }

    pub fn get_latest(&self, place: &Place<'tcx>) -> Location {
        self.latest.get(place)
    }

    pub fn reborrows_blocking(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<&Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|rb| rb.blocked_place == place)
            .collect()
    }

    pub fn reborrows_assigned_to(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<&Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|rb| rb.assigned_place == place)
            .collect()
    }

    pub fn add_region_projection_member(&mut self, member: RegionProjectionMember<'tcx>) {
        self.region_projection_members.insert(member);
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: ty::Region<'tcx>,
    ) {
        self.reborrows
            .add_reborrow(blocked_place, assigned_place, mutability, location, region);
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.reborrows.has_reborrow_at_location(location)
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({})
    }

    pub fn new(body: &'mir mir::Body<'tcx>) -> Self {
        Self {
            body,
            region_projection_members: RegionProjectionMembers::new(),
            deref_expansions: DerefExpansions::new(),
            latest: Latest::new(),
            reborrows: ReborrowingDag::new(),
            region_abstractions: RegionAbstractions::new(),
        }
    }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        self.region_abstractions.insert(abstraction);
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) {
        self.reborrows
            .make_place_old(place, &self.latest, debug_ctx);
        self.deref_expansions.make_place_old(place, &self.latest);
        self.region_abstractions.make_place_old(place, &self.latest);
    }
}
