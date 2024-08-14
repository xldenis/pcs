use crate::rustc_interface::middle::mir::{BasicBlock, Location};

use super::{Place, PlaceRepacker};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum SnapshotLocation {
    Location(Location),
    Join(BasicBlock),
}

impl From<Location> for SnapshotLocation {
    fn from(loc: Location) -> Self {
        SnapshotLocation::Location(loc)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct PlaceSnapshot<'tcx> {
    pub place: Place<'tcx>,
    pub at: SnapshotLocation,
}

impl<'tcx> PlaceSnapshot<'tcx> {
    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: T) -> Self {
        PlaceSnapshot {
            place,
            at: at.into(),
        }
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceSnapshot<'tcx> {
        PlaceSnapshot {
            place: self.place.project_deref(repacker),
            at: self.at,
        }
    }
}
