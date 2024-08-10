use std::{collections::BTreeSet, rc::Rc};

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::{
        fx::{FxHashMap, FxHashSet},
        graph::dominators::Dominators,
    },
    dataflow::{AnalysisDomain, JoinSemiLattice},
    hir::def_id::DefId,
    middle::mir::{
        self, tcx::PlaceTy, BasicBlock, Local, Location, Operand, PlaceElem, VarDebugInfo,
    },
    middle::ty::{self, GenericArgsRef, RegionVid, TyCtxt},
};

use crate::{
    combined_pcs::UnblockEdge,
    free_pcs::CapabilityProjections,
    rustc_interface,
    utils::{Place, PlaceSnapshot},
    ReborrowBridge,
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionType<'tcx> {
    FunctionCall {
        location: Location,

        def_id: DefId,

        substs: GenericArgsRef<'tcx>,

        edges: Vec<(usize, AbstractionBlockEdge<'tcx>)>,
    },
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct AbstractionBlockEdge<'tcx> {
    pub input: AbstractionTarget<'tcx>,
    pub output: AbstractionTarget<'tcx>,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum AbstractionTarget<'tcx> {
    MaybeOldPlace(MaybeOldPlace<'tcx>),
    RegionProjection(RegionProjection<'tcx>),
}

impl<'tcx> AbstractionTarget<'tcx> {
    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        match self {
            AbstractionTarget::MaybeOldPlace(p) => p == place,
            AbstractionTarget::RegionProjection(p) => false,
        }
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        match self {
            AbstractionTarget::MaybeOldPlace(p) => p.make_place_old(place, latest),
            AbstractionTarget::RegionProjection(p) => p.make_place_old(place, latest),
        }
    }

    pub fn region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> RegionVid {
        match self {
            AbstractionTarget::MaybeOldPlace(p) => {
                let prefix = p.place().prefix_place(repacker);
                match prefix.unwrap().ty(repacker).ty.kind() {
                    ty::Ref(region, _, _) => match region.kind() {
                        ty::RegionKind::ReVar(v) => v,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            }
            AbstractionTarget::RegionProjection(p) => p.region,
        }
    }
}

impl<'tcx> AbstractionType<'tcx> {
    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall { location, .. } => *location,
        }
    }

    pub fn inputs(&self) -> Vec<&AbstractionTarget<'tcx>> {
        match self {
            AbstractionType::FunctionCall { edges, .. } => {
                edges.iter().map(|(_, edge)| &edge.input).collect()
            }
        }
    }
    pub fn outputs(&self) -> Vec<&AbstractionTarget<'tcx>> {
        match self {
            AbstractionType::FunctionCall { edges, .. } => {
                edges.iter().map(|(_, edge)| &edge.output).collect()
            }
        }
    }

    pub fn blocks_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match self {
            AbstractionType::FunctionCall { edges, .. } => edges
                .iter()
                .flat_map(|(_, edge)| match edge.input {
                    AbstractionTarget::MaybeOldPlace(p) => Some(p),
                    AbstractionTarget::RegionProjection(_) => None,
                })
                .collect(),
        }
    }

    pub fn blocker_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match self {
            AbstractionType::FunctionCall { edges, .. } => edges
                .iter()
                .flat_map(|(_, edge)| match edge.output {
                    AbstractionTarget::MaybeOldPlace(p) => Some(p),
                    AbstractionTarget::RegionProjection(_) => None,
                })
                .collect(),
        }
    }

    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.blocks_places().contains(place)
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        match self {
            AbstractionType::FunctionCall { edges, .. } => {
                for (_, edge) in edges {
                    edge.input.make_place_old(place, latest);
                    edge.output.make_place_old(place, latest);
                }
            }
        }
    }
}


fn make_places_old<'tcx>(
    places: FxHashSet<MaybeOldPlace<'tcx>>,
    place: Place<'tcx>,
    location: Location,
) -> FxHashSet<MaybeOldPlace<'tcx>> {
    places
        .into_iter()
        .map(|p| {
            if p.is_current() && place.is_prefix(p.place()) {
                MaybeOldPlace::OldPlace(PlaceSnapshot {
                    place: p.place(),
                    at: location,
                })
            } else {
                p
            }
        })
        .collect()
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current {
            place: place.into(),
        }
    }
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn region_projection(
        &self,
        idx: usize,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx> {
        RegionProjection::new(self.region_projections(repacker)[idx].region, self.clone())
    }

    pub fn region_projections(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RegionProjection<'tcx>> {
        extract_nested_lifetimes(self.ty(repacker).ty)
            .iter()
            .map(|region| RegionProjection::new(get_vid(region).unwrap(), self.clone()))
            .collect()
    }

    pub fn new(place: Place<'tcx>, at: Option<Location>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot { place, at })
        } else {
            Self::Current { place }
        }
    }

    pub fn as_current(&self) -> Option<Place<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => Some(*place),
            MaybeOldPlace::OldPlace(_) => None,
        }
    }

    pub fn old_place(&self) -> Option<PlaceSnapshot<'tcx>> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.clone()),
        }
    }

    pub fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        self.place().ty(repacker)
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(self.place().project_deref(repacker).into(), self.location())
    }
    pub fn project_deeper(&self, tcx: TyCtxt<'tcx>, elem: PlaceElem<'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(
            self.place().project_deeper(&[elem], tcx).into(),
            self.location(),
        )
    }

    pub fn is_mut_ref(&self, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        self.place().is_mut_ref(body, tcx)
    }

    pub fn is_ref(&self, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        self.place().is_ref(body, tcx)
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace(old_place) => old_place.place,
        }
    }

    pub fn location(&self) -> Option<Location> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.at),
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{:?}", loc)),
        })
    }

    pub fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let p = self.place().to_short_string(repacker);
        format!(
            "{}{}",
            p,
            if let Some(location) = self.location() {
                format!(" at {:?}", location)
            } else {
                "".to_string()
            }
        )
    }
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        if self.is_current() && place.is_prefix(self.place()) {
            *self = MaybeOldPlace::OldPlace(PlaceSnapshot {
                place: self.place(),
                at: latest.get(&self.place()),
            });
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Borrow<'tcx> {
    pub borrowed_place: Place<'tcx>,
    pub assigned_place: Place<'tcx>,
    pub is_mut: bool,
}

impl<'tcx> Borrow<'tcx> {
    pub fn new(borrowed_place: Place<'tcx>, assigned_place: Place<'tcx>, is_mut: bool) -> Self {
        Self {
            borrowed_place,
            assigned_place,
            is_mut,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "borrowed_place": self.borrowed_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.is_mut,
        })
    }
}


#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Latest<'tcx>(FxHashMap<Place<'tcx>, Location>);

impl<'tcx> Latest<'tcx> {
    pub fn new() -> Self {
        Self(FxHashMap::default())
    }
    pub fn get(&self, place: &Place<'tcx>) -> Location {
        if let Some(loc) = self.0.get(place) {
            return *loc;
        }
        for (p, _) in place.iter_projections() {
            if let Some(loc) = self.0.get(&p.into()) {
                return *loc;
            }
        }
        Location::START
    }
    pub fn insert(&mut self, place: Place<'tcx>, location: Location) -> Option<Location> {
        self.0.insert(place, location)
    }

    /// Joins the latest versions of locations, by choosing the closest location
    /// that appears after (or at) both locations. If either location definitely
    /// comes after the other, that one is chosen. Otherwise, we return the
    /// first block that dominates both locations. Such a block definitely
    /// exists (presumably it is the block where this join occurs)
    pub fn join(&mut self, other: &Self, body: &mir::Body<'tcx>) -> bool {
        let mut changed = false;
        for (place, other_loc) in other.0.iter() {
            if let Some(self_loc) = self.0.get(place) {
                let dominators = body.basic_blocks.dominators();
                let new_loc = join_locations(*self_loc, *other_loc, dominators);
                if new_loc != *self_loc {
                    self.insert(*place, new_loc);
                    changed = true;
                }
            } else {
                self.insert(*place, *other_loc);
                changed = true;
            }
        }
        changed
    }
}

/// Choses the closes location that appears after or at both locations. If
/// either location definitely comes after the other, that one is chosen.
/// Otherwise, we return the first block that dominates both locations. Such a
/// block definitely exists (presumably it is the block where this join occurs)
fn join_locations(loc1: Location, loc2: Location, dominators: &Dominators<BasicBlock>) -> Location {
    if loc1.dominates(loc2, dominators) {
        loc1
    } else if loc2.dominates(loc1, dominators) {
        loc2
    } else {
        for block in dominators.dominators(loc2.block) {
            if dominators.dominates(block, loc1.block) {
                return Location {
                    block,
                    statement_index: 0,
                };
            }
        }
        unreachable!()
    }
}

use crate::utils::PlaceRepacker;
use serde_json::{json, Value};

use super::{
    borrows_state::BorrowsState, borrows_visitor::{extract_nested_lifetimes, get_vid}, deref_expansions::DerefExpansions, engine::ReborrowAction, path_condition::PathConditions, reborrowing_dag::ReborrowingDag
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Reborrow<'tcx> {
    pub blocked_place: MaybeOldPlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    pub mutability: Mutability,

    /// The location when the reborrow was created
    pub location: Location,

    pub region: ty::Region<'tcx>,
}

impl<'tcx> Reborrow<'tcx> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.blocked_place.make_place_old(place, latest);
        self.assigned_place.make_place_old(place, latest);
    }

    pub fn assiged_place_region_vid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<RegionVid> {
        match self
            .assigned_place
            .place()
            .prefix_place(repacker)
            .unwrap()
            .ty(repacker)
            .ty
            .kind()
        {
            ty::Ref(region, _, _) => match region.kind() {
                ty::RegionKind::ReVar(v) => Some(v),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn region_vid(&self) -> Option<RegionVid> {
        match self.region.kind() {
            ty::RegionKind::ReVar(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "blocked_place": self.blocked_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.mutability == Mutability::Mut
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct RegionProjection<'tcx> {
    pub place: MaybeOldPlace<'tcx>,
    pub region: RegionVid,
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn new(region: RegionVid, place: MaybeOldPlace<'tcx>) -> Self {
        Self { place, region }
    }
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.place.make_place_old(place, latest);
    }
    pub fn index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.place
            .place()
            .projection_index(self.region, repacker)
            .unwrap()
    }
}
