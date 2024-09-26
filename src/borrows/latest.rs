use std::collections::BTreeMap;

use crate::rustc_interface::middle::mir::{BasicBlock, Local, Location};
use crate::utils::{Place, SnapshotLocation};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Latest(BTreeMap<Local, SnapshotLocation>);

impl Latest {
    pub fn new() -> Self {
        Self(BTreeMap::default())
    }
    pub fn get<'tcx>(&self, place: &Place<'tcx>) -> SnapshotLocation {
        self.0
            .get(&place.local)
            .cloned()
            .unwrap_or(SnapshotLocation::Location(Location::START))
    }
    pub fn insert(&mut self, local: Local, location: SnapshotLocation) -> Option<SnapshotLocation> {
        self.0.insert(local, location)
    }

    pub fn join(&mut self, other: &Self, block: BasicBlock) -> bool {
        let mut changed = false;
        for (place, other_loc) in other.0.iter() {
            if let Some(self_loc) = self.0.get(place) {
                if *self_loc != *other_loc {
                    self.insert(*place, SnapshotLocation::Join(block));
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
