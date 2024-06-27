use std::rc::Rc;

use rustc_interface::{
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, Location, VarDebugInfo},
};

use crate::{rustc_interface, utils::Place};

impl<'tcx> JoinSemiLattice for BorrowsState<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for borrow in &other.borrows {
            if self.borrows.insert(borrow.clone()) {
                changed = true;
            }
        }
        for region_abstraction in &other.region_abstractions {
            if !self.region_abstractions.contains(region_abstraction) {
                self.region_abstractions.push(region_abstraction.clone());
                changed = true;
            }
        }
        changed
    }
}

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

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum MaybeOldPlace<'tcx> {
    Current {
        place: Place<'tcx>,
    },
    OldPlace {
        place: Place<'tcx>,
        before: Location,
    },
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace { place, .. } => *place,
        }
    }

    pub fn before_location(&self) -> Option<Location> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace { before, .. } => Some(*before),
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        let place_str = match self.place().to_string(repacker) {
            crate::utils::display::PlaceDisplay::Temporary(p) => format!("{:?}", p),
            crate::utils::display::PlaceDisplay::User(_, s) => s,
        };

        json!({
            "place": place_str,
            "before": self.before_location().map(|loc| format!("{:?}", loc)),
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Borrow<'tcx> {
    pub kind: BorrowKind,
    pub borrowed_place: MaybeOldPlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    pub is_mut: bool,
}

impl<'tcx> Borrow<'tcx> {
    pub fn new(
        kind: BorrowKind,
        borrowed_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        is_mut: bool,
    ) -> Self {
        Self {
            kind,
            borrowed_place: MaybeOldPlace::Current {
                place: borrowed_place,
            },
            assigned_place: MaybeOldPlace::Current {
                place: assigned_place,
            },
            is_mut,
        }
    }

    pub fn is_current(&self) -> bool {
        self.borrowed_place.is_current() && self.assigned_place.is_current()
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "kind": format!("{:?}", self.kind),
            "borrowed_place": self.borrowed_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.is_mut,
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum BorrowKind {
    Rustc(BorrowIndex),
    PCS,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsState<'tcx> {
    pub borrows: FxHashSet<Borrow<'tcx>>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
}

use crate::utils::PlaceRepacker;
use serde_json::{json, Value};

use super::engine::BorrowAction;

impl<'tcx> BorrowsState<'tcx> {
    pub fn contains_borrow(&self, borrow: &Borrow<'tcx>) -> bool {
        self.borrows.contains(borrow)
    }

    pub fn apply_action(&mut self, action: BorrowAction<'_, 'tcx>) {
        match action {
            BorrowAction::AddBorrow(borrow) => self.borrows.insert(borrow.into_owned()),
            BorrowAction::RemoveBorrow(borrow) => self.borrows.remove(borrow),
        };
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({
            "borrows": self.borrows.iter().map(|borrow| {
                borrow.to_json(repacker)
            }).collect::<Vec<_>>(),
        })
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub fn new() -> Self {
        Self {
            borrows: FxHashSet::default(),
            region_abstractions: vec![],
        }
    }

    pub fn live_borrows(&self) -> impl Iterator<Item = &Borrow<'tcx>> {
        self.borrows.iter().filter(|borrow| {
            borrow.assigned_place.is_current() && borrow.borrowed_place.is_current()
        })
    }

    pub fn reference_targeting_place(
        &self,
        place: Place<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
    ) -> Option<Place<'tcx>> {
        self.live_borrows()
            .find(|borrow| {
                borrow.borrowed_place.is_current() && borrow.borrowed_place.place() == place
            })
            .map(|borrow| borrow.assigned_place.place())
    }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        if !self.region_abstractions.contains(&abstraction) {
            self.region_abstractions.push(abstraction);
        }
    }

    pub fn add_borrow(&mut self, borrow: Borrow<'tcx>) {
        self.borrows.insert(borrow);
    }

    pub fn add_rustc_borrow(&mut self, borrow: BorrowIndex, borrow_set: &BorrowSet<'tcx>) {
        self.borrows.insert(Borrow::new(
            BorrowKind::Rustc(borrow),
            borrow_set[borrow].borrowed_place.into(),
            borrow_set[borrow].assigned_place.into(),
            matches!(borrow_set[borrow].kind, mir::BorrowKind::Mut { .. }),
        ));
    }

    pub fn remove_rustc_borrow(&mut self, borrow: &BorrowIndex) {
        self.borrows
            .retain(|b| !b.is_current() || b.kind != BorrowKind::Rustc(*borrow));
    }
}
