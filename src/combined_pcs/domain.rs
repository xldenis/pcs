// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use rustc_interface::{
    dataflow::fmt::DebugWithContext, dataflow::JoinSemiLattice, middle::mir,
    middle::mir::BasicBlock,
};

use crate::{
    borrows::{
        borrows_visitor::DebugCtx,
        domain::{MaybeOldPlace, ReborrowBlockedPlace},
        engine::BorrowsDomain,
        unblock_graph::UnblockGraph,
    },
    free_pcs::{CapabilityLocal, FreePlaceCapabilitySummary},
    rustc_interface,
    visualization::generate_dot_graph,
};

use super::{PcsContext, PcsEngine};

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    pub cgx: Rc<PcsContext<'a, 'tcx>>,
    pub block: BasicBlock,

    pub fpcs: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub borrows: BorrowsDomain<'a, 'tcx>,

    /// For debugging, how many times this block has been seen to compute dataflow
    pub iteration: usize,

    /// For debugging, where to write output DOT files for this block
    pub dot_output_dir: Option<String>,
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    pub fn new(
        cgx: Rc<PcsContext<'a, 'tcx>>,
        block: BasicBlock,
        dot_output_dir: Option<String>,
    ) -> Self {
        let fpcs = FreePlaceCapabilitySummary::new(cgx.rp);
        let borrows = BorrowsDomain::new(cgx.rp, block);
        Self {
            cgx,
            block,
            fpcs,
            borrows,
            iteration: 0,
            dot_output_dir,
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
        if let Some(dir) = &self.dot_output_dir
            && self.iteration == 0
        {
            let file_path = format!("{}/join_{}_0.dot", dir, self.block.index());
            generate_dot_graph(
                self.cgx.rp,
                &self.fpcs.after,
                &self.borrows.after,
                &self.cgx.mir.borrow_set,
                &file_path,
            )
            .unwrap();
        }
        self.iteration += 1;
        let fpcs = self.fpcs.join(&other.fpcs);
        let borrows = self.borrows.join(&other.borrows);
        let mut g = UnblockGraph::new();
        for root in self.borrows.after.roots(self.cgx.rp) {
            if let ReborrowBlockedPlace::Local(MaybeOldPlace::Current { place: root }) = root {
                match &self.fpcs.after[root.local] {
                    CapabilityLocal::Unallocated => {
                        g.unblock_place(root.into(), &self.borrows.after, self.cgx.rp);
                    }
                    CapabilityLocal::Allocated(projs) => {
                        if !(*projs).contains_key(&root) {
                            g.unblock_place(root.into(), &self.borrows.after, self.cgx.rp);
                        }
                    }
                }
            }
        }
        let ub = self.borrows.after.apply_unblock_graph(
            g,
            self.cgx.rp,
            mir::Location {
                block: self.block,
                statement_index: 0,
            },
        );
        let result = fpcs || borrows || ub;
        if let Some(dir) = &self.dot_output_dir {
            let file_path = format!(
                "{}/join_{:?}_with_{:?}_{}.dot",
                dir, self.block, other.block, self.iteration
            );
            generate_dot_graph(
                self.cgx.rp,
                &self.fpcs.after,
                &self.borrows.after,
                &self.cgx.mir.borrow_set,
                &file_path,
            )
            .unwrap()
        }
        result
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
