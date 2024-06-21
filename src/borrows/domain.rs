use std::rc::Rc;

use rustc_interface::{
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, Location},
};

use crate::{rustc_interface, utils::Place};

impl<'tcx> JoinSemiLattice for BorrowsDomain<'tcx> {
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
        for action in &other.actions {
            if !self.actions.contains(action) {
                self.actions.insert(action.clone());
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
pub struct Borrow<'tcx> {
    pub kind: BorrowKind<'tcx>,
    pub borrowed_place_before: Option<Location>,
    pub assigned_place_before: Option<Location>,
}

impl<'tcx> Borrow<'tcx> {
    pub fn new(
        kind: BorrowKind<'tcx>,
        borrowed_place_before: Option<Location>,
        assigned_place_before: Option<Location>,
    ) -> Self {
        Self {
            kind,
            borrowed_place_before,
            assigned_place_before,
        }
    }

    pub fn assigned_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        self.kind.assigned_place(borrow_set)
    }

    pub fn borrowed_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        self.kind.borrowed_place(borrow_set)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum BorrowKind<'tcx> {
    Rustc(BorrowIndex),
    PCS {
        borrowed_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
    },
}

impl<'tcx> BorrowKind<'tcx> {
    pub fn assigned_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        match self {
            BorrowKind::Rustc(borrow_index) => borrow_set[*borrow_index].assigned_place.into(),
            BorrowKind::PCS { assigned_place, .. } => *assigned_place,
        }
    }

    pub fn borrowed_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        match self {
            BorrowKind::Rustc(borrow_index) => borrow_set[*borrow_index].borrowed_place.into(),
            BorrowKind::PCS { borrowed_place, .. } => *borrowed_place,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsDomain<'tcx> {
    pub borrows: FxHashSet<Borrow<'tcx>>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
    pub actions: FxHashSet<String>,
}

use serde_json::{json, Value};
use crate::utils::PlaceRepacker;

impl<'tcx> BorrowsDomain<'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({
            "borrows": self.borrows.iter().map(|borrow| {
                json!({
                    "kind": match &borrow.kind {
                        BorrowKind::Rustc(index) => json!(format!("Rustc({:?})", index)),
                        BorrowKind::PCS { borrowed_place, assigned_place } => json!({
                            "PCS": {
                                "borrowed_place": format!("{:?}", borrowed_place.to_string(repacker)),
                                "assigned_place": format!("{:?}", assigned_place.to_string(repacker))
                            }
                        })
                    },
                    "target_place_before": format!("{:?}", borrow.borrowed_place_before),
                    "assigned_place_before": format!("{:?}", borrow.assigned_place_before)
                })
            }).collect::<Vec<_>>(),
            "actions": self.actions.iter().collect::<Vec<_>>()
        })
    }
}


impl<'tcx> BorrowsDomain<'tcx> {
    pub fn new() -> Self {
        Self {
            borrows: FxHashSet::default(),
            region_abstractions: vec![],
            actions: FxHashSet::default(),
        }
    }

    pub fn reference_targeting_place(
        &self,
        place: Place<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
    ) -> Option<Place<'tcx>> {
        self.borrows
            .iter()
            .find(|borrow| borrow.borrowed_place(borrow_set) == place)
            .map(|borrow| borrow.assigned_place(borrow_set))
    }

    pub fn log_action(&mut self, action: String) {
        self.actions.insert(action);
    }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        if !self.region_abstractions.contains(&abstraction) {
            self.region_abstractions.push(abstraction);
        }
    }

    pub fn add_borrow(&mut self, borrow: Borrow<'tcx>) {
        self.borrows.insert(borrow);
    }

    pub fn add_rustc_borrow(&mut self, borrow: BorrowIndex) {
        self.borrows.insert(Borrow {
            kind: BorrowKind::Rustc(borrow),
            borrowed_place_before: None,
            assigned_place_before: None,
        });
    }

    pub fn remove_borrow(&mut self, borrow: &BorrowIndex) {
        self.borrows.remove(&Borrow {
            kind: BorrowKind::Rustc(*borrow),
            borrowed_place_before: None,
            assigned_place_before: None,
        });
    }
}
