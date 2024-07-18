use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::{
        fx::{FxHashMap, FxHashSet},
        graph::dominators::Dominators,
    },
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Local, Location, VarDebugInfo},
    middle::ty::TyCtxt,
};

use crate::{
    combined_pcs::UnblockGraph,
    free_pcs::CapabilityProjections,
    rustc_interface,
    utils::{Place, PlaceSnapshot},
    ReborrowBridge,
};
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RegionAbstraction<'tcx> {
    pub loans_in: FxHashSet<mir::Place<'tcx>>,
    pub loans_out: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> RegionAbstraction<'tcx> {
    pub fn new() -> Self {
        Self {
            loans_in: FxHashSet::default(),
            loans_out: FxHashSet::default(),
        }
    }

    pub fn add_loan_in(&mut self, loan: mir::Place<'tcx>) {
        self.loans_in.insert(loan);
    }

    pub fn add_loan_out(&mut self, loan: mir::Place<'tcx>) {
        self.loans_out.insert(loan);
    }
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
        match self {
            MaybeOldPlace::Current { place } => place.ty(repacker),
            MaybeOldPlace::OldPlace(old_place) => old_place.place.ty(repacker),
        }
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => MaybeOldPlace::Current {
                place: place.project_deref(repacker),
            },
            MaybeOldPlace::OldPlace(old_place) => {
                MaybeOldPlace::OldPlace(old_place.project_deref(repacker))
            }
        }
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
    expansion: Vec<Place<'tcx>>,
    pub location: Location,
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn new(base: MaybeOldPlace<'tcx>, expansion: Vec<Place<'tcx>>, location: Location) -> Self {
        Self {
            base,
            expansion,
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
            "expansion": self.expansion.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }

    pub fn expansion(&self) -> Vec<MaybeOldPlace<'tcx>> {
        self.expansion
            .iter()
            .map(|p| MaybeOldPlace::new(*p, self.base.location()))
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
