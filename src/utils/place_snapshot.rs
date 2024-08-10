use crate::rustc_interface::{
    middle::mir::{Location},
};

use super::{Place, PlaceRepacker};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct PlaceSnapshot<'tcx> {
    pub place: Place<'tcx>,
    pub at: Location,
}

impl<'tcx> PlaceSnapshot<'tcx> {
    pub fn new(place: Place<'tcx>, at: Location) -> Self {
        PlaceSnapshot { place, at }
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceSnapshot<'tcx> {
        PlaceSnapshot {
            place: self.place.project_deref(repacker),
            at: self.at,
        }
    }
}
