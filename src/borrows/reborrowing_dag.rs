use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, BasicBlock, Location, VarDebugInfo},
    middle::ty::TyCtxt,
};

use crate::{rustc_interface, utils::Place};

use super::domain::{MaybeOldPlace, Reborrow};
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ReborrowingDag<'tcx> {
    reborrows: FxHashSet<Reborrow<'tcx>>,
}

impl<'tcx> ReborrowingDag<'tcx> {
    pub fn remove(&mut self, reborrow: &Reborrow<'tcx>) -> bool {
        self.reborrows.remove(reborrow)
    }
    pub fn assigned_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.reborrows.iter().map(|r| r.assigned_place).collect()
    }
    pub fn make_place_old(&mut self, place: Place<'tcx>, location: Location) {
        let mut new = FxHashSet::default();
        for mut reborrow in self.reborrows.clone() {
            if reborrow.blocked_place.is_current() && reborrow.blocked_place.place() == place {
                reborrow.blocked_place = MaybeOldPlace::new(place, Some(location));
            }
            if reborrow.assigned_place.is_current() && reborrow.assigned_place.place() == place {
                reborrow.assigned_place = MaybeOldPlace::new(place, Some(location));
            }
            new.insert(reborrow);
        }
        self.reborrows = new;
    }

    pub fn reborrows_blocked_by(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|r| r.assigned_place == place)
            .cloned()
            .collect()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Reborrow<'tcx>> {
        self.reborrows.iter()
    }

    pub fn new() -> Self {
        Self {
            reborrows: FxHashSet::default(),
        }
    }

    pub fn contains(&self, reborrow: &Reborrow<'tcx>) -> bool {
        self.reborrows.contains(reborrow)
    }

    pub fn has_reborrow_at_location(
        &self,
        from: Place<'tcx>,
        to: Place<'tcx>,
        location: Location,
    ) -> bool {
        self.reborrows.iter().any(|reborrow| {
            reborrow.blocked_place.place() == from
                && reborrow.assigned_place.place() == to
                && reborrow.location == location
        })
    }

    pub fn ensure_acyclic(&self) {
        let mut reborrows = self.reborrows.clone();
        while reborrows.len() > 0 {
            let old_reborrows = reborrows.clone();
            reborrows.retain(|reborrow| {
                old_reborrows
                    .iter()
                    .any(|ob| ob.blocked_place == reborrow.assigned_place)
            });
            if reborrows.len() == old_reborrows.len() {
                panic!("Cycle")
            }
        }
    }

    pub fn roots(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        let mut candidates: FxHashSet<MaybeOldPlace<'tcx>> =
            self.reborrows.iter().map(|r| r.blocked_place).collect();
        for reborrow in self.reborrows.iter() {
            candidates.remove(&reborrow.assigned_place);
        }
        candidates
    }

    pub fn get_places_blocking(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.reborrows
            .iter()
            .filter(|r| r.blocked_place == place)
            .map(|r| r.assigned_place)
            .collect()
    }

    pub fn get_places_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.reborrows
            .iter()
            .filter(|r| r.assigned_place == place)
            .map(|r| r.blocked_place)
            .collect()
    }

    pub fn insert(&mut self, reborrow: Reborrow<'tcx>) -> bool {
        assert!(reborrow.blocked_place != reborrow.assigned_place);
        assert!(
            reborrow.assigned_place.place().is_deref(),
            "Place {:?} must be a dereference",
            reborrow.assigned_place
        );
        let result = self.reborrows.insert(reborrow);
        self.ensure_acyclic();
        result
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
    ) -> bool {
        self.insert(Reborrow {
            mutability,
            blocked_place: MaybeOldPlace::Current {
                place: blocked_place,
            },
            assigned_place: MaybeOldPlace::Current {
                place: assigned_place,
            },
            location,
        })
    }
    pub fn kill_reborrows_blocking(&mut self, blocked_place: MaybeOldPlace<'tcx>) -> bool {
        let mut changed = false;
        for to_remove in self.reborrows.clone().iter() {
            if to_remove.blocked_place == blocked_place {
                if self.reborrows.remove(to_remove) {
                    changed = true;
                }
            }
        }
        changed
    }

    pub fn kill_reborrows_assigned_to(&mut self, assigned_place: MaybeOldPlace<'tcx>) -> bool {
        let mut changed = false;
        for to_remove in self.reborrows.clone().iter() {
            if to_remove.assigned_place == assigned_place {
                if self.reborrows.remove(to_remove) {
                    changed = true;
                }
            }
        }
        changed
    }

    pub fn kill_reborrows(
        &mut self,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
    ) -> bool {
        let mut changed = false;
        for to_remove in self.reborrows.clone().iter() {
            if to_remove.blocked_place == blocked_place
                && to_remove.assigned_place == assigned_place
            {
                if self.reborrows.remove(to_remove) {
                    changed = true;
                }
            }
        }
        changed
    }

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        let mut new = FxHashSet::default();
        for mut reborrow in self.reborrows.clone() {
            if reborrow.assigned_place == orig_assigned_place {
                reborrow.assigned_place = new_assigned_place;
            }
            new.insert(reborrow);
        }
        self.reborrows = new;
    }
}
