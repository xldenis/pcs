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

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.reborrows.retain(|reborrow| {
            path.contains(&reborrow.location.block)
        });
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

    pub fn get_place_blocking(&self, place: MaybeOldPlace<'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        self.reborrows.iter().find(|r| r.assigned_place == place).map(|r| r.blocked_place)
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
            location
        })
    }

    pub fn kill_reborrow_blocking(
        &mut self,
        place: MaybeOldPlace<'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        let to_remove = self
            .reborrows
            .iter()
            .find(|reborrow| reborrow.blocked_place == place)
            .cloned();
        if let Some(to_remove) = to_remove {
            self.reborrows.remove(&to_remove);
            Some(to_remove.assigned_place)
        } else {
            None
        }
    }
}
