use crate::utils::Place;

use super::domain::{Borrow, MaybeOldPlace, Reborrow};
use crate::rustc_interface::middle::{
    mir::Location,
    ty::RegionVid,
};

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum UnblockReason<'tcx> {
    RemoveBorrow(Borrow<'tcx>),
    ReborrowBlocksPlace(Reborrow<'tcx>, MaybeOldPlace<'tcx>),
    KillPlace(MaybeOldPlace<'tcx>),
    KillReborrow(Reborrow<'tcx>),
    Unallocated(Place<'tcx>),
    NotInProjection(Place<'tcx>),
    ReborrowAssignedTo(Reborrow<'tcx>, MaybeOldPlace<'tcx>),
    KillReborrowAssignedPlace(Reborrow<'tcx>, MaybeOldPlace<'tcx>),
    Projection(MaybeOldPlace<'tcx>),
    NotInStateToBridge(Reborrow<'tcx>),
    DerefExpansionDoesntExist(Place<'tcx>, Location),
    EnsureExpansionTo(MaybeOldPlace<'tcx>),
    FpcsCollapse(MaybeOldPlace<'tcx>),
    KillAbstraction(RegionVid),
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct UnblockReasons<'tcx>(Vec<UnblockReason<'tcx>>);

impl<'tcx> UnblockReasons<'tcx> {
    pub fn new(reason: UnblockReason<'tcx>) -> Self {
        Self(vec![reason])
    }
    pub fn add(mut self, reason: UnblockReason<'tcx>) -> Self {
        assert!(
            !self.0.contains(&reason),
            "Already saw reason {reason:#?} unblock this: {:#?}",
            self
        );
        self.0.push(reason);
        self
    }
    pub fn merge(mut self, mut other: Self) -> Self {
        self.0.append(&mut other.0);
        self
    }
}
