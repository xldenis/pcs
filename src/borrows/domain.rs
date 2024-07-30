use std::rc::Rc;

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
    middle::ty::{self, RegionVid, TyCtxt, GenericArgsRef},
};

use crate::{
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

        /// For each (i, p) in args, `i` is the index of the argument in the
        /// function definition, `p` is the place that was used as the argument
        blocks_args: Vec<(usize, MaybeOldPlace<'tcx>)>,

        /// The blocked place; e.g. for a function that returns a reference, this
        /// would be the dereference of the target of the call
        /// TODO: Actually multiple places may be blocked...
        blocked_place: MaybeOldPlace<'tcx>,
    },
}

impl<'tcx> AbstractionType<'tcx> {
    pub fn location(&self) -> Location {
        match self {
            AbstractionType::FunctionCall { location, .. } => *location,
        }
    }

    pub fn blocked_by_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match self {
            AbstractionType::FunctionCall { blocked_place, .. } => {
                vec![blocked_place.clone()].into_iter().collect()
            }
        }
    }
    pub fn blocks_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match self {
            AbstractionType::FunctionCall { blocks_args, .. } => {
                blocks_args.iter().map(|(_, arg)| arg.clone()).collect()
            }
        }
    }

    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        match self {
            AbstractionType::FunctionCall { blocks_args, .. } => {
                blocks_args.iter().any(|(_, arg)| arg == place)
            }
        }
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, location: Location) {
        match self {
            AbstractionType::FunctionCall {
                blocks_args,
                blocked_place,
                ..
            } => {
                for (i, arg) in blocks_args.iter_mut() {
                    if arg.is_current() && place.is_prefix(arg.place()) {
                        *arg = MaybeOldPlace::OldPlace(PlaceSnapshot {
                            place: arg.place(),
                            at: location,
                        });
                    }
                }
                if blocked_place.is_current() && place.is_prefix(blocked_place.place()) {
                    *blocked_place = MaybeOldPlace::OldPlace(PlaceSnapshot {
                        place: blocked_place.place(),
                        at: location,
                    });
                }
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RegionAbstraction<'tcx> {
    pub region: RegionVid,

    /// The regions blocked by this region
    pub blocks_abstractions: FxHashSet<RegionVid>,

    pub abstraction_type: AbstractionType<'tcx>,
}

impl<'tcx> RegionAbstraction<'tcx> {
    pub fn new(region: RegionVid, abstraction_type: AbstractionType<'tcx>) -> Self {
        Self {
            region,
            blocks_abstractions: FxHashSet::default(),
            abstraction_type,
        }
    }

    pub fn location(&self) -> Location {
        self.abstraction_type.location()
    }

    pub fn blocks_abstraction(&self, region: RegionVid) -> bool {
        self.blocks_abstractions.contains(&region)
    }

    pub fn blocks(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.abstraction_type.blocks(&place)
    }

    pub fn blocks_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocks_places()
    }

    pub fn blocked_by_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocked_by_places()
    }

    /// Add a region that this region blocks
    pub fn add_blocked_abstraction(&mut self, vid: RegionVid) {
        self.blocks_abstractions.insert(vid);
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, location: Location) {
        self.abstraction_type.make_place_old(place, location);
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
    pub fn new(place: Place<'tcx>, at: Option<Location>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot { place, at })
        } else {
            Self::Current { place }
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

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct DerefExpansion<'tcx> {
    pub base: MaybeOldPlace<'tcx>,
    pub expansion: Vec<PlaceElem<'tcx>>,
    pub location: Location,
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn new(base: MaybeOldPlace<'tcx>, expansion: Vec<Place<'tcx>>, location: Location) -> Self {
        assert!(expansion.iter().all(|p| base.place().is_prefix(*p)
            && p.projection.len() == base.place().projection.len() + 1));
        Self {
            base,
            expansion: expansion
                .into_iter()
                .map(|p| p.projection.last().unwrap())
                .copied()
                .collect(),
            location,
        }
    }

    pub fn make_base_old(&mut self, place_location: Location) {
        assert!(self.base.is_current());
        self.base = MaybeOldPlace::OldPlace(PlaceSnapshot {
            place: self.base.place(),
            at: place_location,
        });
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(repacker),
            "expansion": self.expansion(repacker.tcx()).iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }

    pub fn expansion(&self, tcx: TyCtxt<'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        self.expansion
            .iter()
            .map(|p| self.base.project_deeper(tcx, *p))
            .collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Latest<'tcx>(FxHashMap<Place<'tcx>, Location>);

impl<'tcx> Latest<'tcx> {
    pub fn new() -> Self {
        Self(FxHashMap::default())
    }
    pub fn get(&self, place: &Place<'tcx>) -> Location {
        self.0.get(place).copied().unwrap_or(Location::START)
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
    borrows_state::BorrowsState, deref_expansions::DerefExpansions, engine::ReborrowAction,
    reborrowing_dag::ReborrowingDag,
};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct Reborrow<'tcx> {
    pub blocked_place: MaybeOldPlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    pub mutability: Mutability,

    /// The location when the reborrow was created
    pub location: Location,
}

impl<'tcx> Reborrow<'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "blocked_place": self.blocked_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.mutability == Mutability::Mut
        })
    }
}
