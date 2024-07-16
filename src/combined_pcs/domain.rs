// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cell::{Cell, RefCell},
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use derive_more::{Deref, DerefMut};
use rustc_interface::{
    dataflow::fmt::DebugWithContext,
    dataflow::JoinSemiLattice,
    index::IndexVec,
    middle::mir::{BasicBlock, Location, START_BLOCK},
};

use crate::{
    borrows::engine::{BorrowsDomain, ReborrowAction},
    free_pcs::{
        CapabilityLocal, CapabilityProjections, FreePlaceCapabilitySummary, HasFpcs, RepackOp,
    },
    rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::{PcsContext, PcsEngine, UnblockGraph};
use crate::borrows::domain::BorrowsState;

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    pub cgx: Rc<PcsContext<'a, 'tcx>>,
    pub block: BasicBlock,

    pub fpcs: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub borrows: BorrowsDomain<'a, 'tcx>,
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    pub fn new(cgx: Rc<PcsContext<'a, 'tcx>>, block: BasicBlock) -> Self {
        let fpcs = FreePlaceCapabilitySummary::new(cgx.rp);
        let borrows = BorrowsDomain::new(&cgx.mir.body);
        Self {
            cgx,
            block,
            fpcs,
            borrows,
        }
    }
}

impl Eq for PlaceCapabilitySummary<'_, '_> {}
impl PartialEq for PlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.fpcs == other.fpcs && self.borrows == other.borrows
    }
}
impl Debug for PlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}\n{:?}", self.fpcs, self.borrows)
    }
}

impl JoinSemiLattice for PlaceCapabilitySummary<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        let fpcs = self.fpcs.join(&other.fpcs);
        let borrows = self.borrows.join(&other.borrows);
        let mut g = UnblockGraph::new();
        for root in self.borrows.after.reborrow_roots() {
            match &self.fpcs.after[root.local] {
                CapabilityLocal::Unallocated => {
                    g.unblock_place(
                        crate::borrows::domain::MaybeOldPlace::Current { place: root },
                        &self.borrows.after,
                        self.block, // TODO: Check
                    );
                }
                CapabilityLocal::Allocated(projs) => {
                    if !(*projs).contains_key(&root) {
                        g.unblock_place(
                            crate::borrows::domain::MaybeOldPlace::Current { place: root },
                            &self.borrows.after,
                            self.block, // TODO: Check
                        );
                    }
                }
            }
        }
        let ub = self.borrows.after.apply_unblock_graph(g);
        fpcs || borrows || ub
    }
}

impl<'a, 'tcx> DebugWithContext<PcsEngine<'a, 'tcx>> for PlaceCapabilitySummary<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &PcsEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        self.fpcs.fmt_diff_with(&old.fpcs, &ctxt.fpcs, f)
    }
}
