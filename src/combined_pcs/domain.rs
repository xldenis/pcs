// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;
use std::{
    collections::BTreeMap,
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use rustc_interface::{
    dataflow::fmt::DebugWithContext,
    dataflow::JoinSemiLattice,
    middle::mir,
    middle::mir::{BasicBlock, Location},
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
    utils::SnapshotLocation,
    visualization::generate_dot_graph,
};

use super::{PcsContext, PcsEngine};

#[derive(Copy, Clone)]
pub struct DataflowIterationDebugInfo {
    pub join_with: BasicBlock,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd)]
pub enum DataflowStmtPhase {
    Initial,
    Join(BasicBlock),
    BeforeStart,
    BeforeAfter,
    Start,
    After,
}

impl DataflowStmtPhase {
    pub fn to_filename_str_part(&self) -> String {
        match self {
            DataflowStmtPhase::Join(block) => format!("join_{:?}", block),
            _ => format!("{:?}", self),
        }
    }
}

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    pub cgx: Rc<PcsContext<'a, 'tcx>>,
    pub block: BasicBlock,

    pub fpcs: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub borrows: BorrowsDomain<'a, 'tcx>,

    pub dot_graphs: DotGraphs,

    dot_output_dir: Option<String>,
}

/// Outermost Vec can be considered a map StatementIndex -> Vec<BTreeMap<DataflowStmtPhase, String>>
/// The inner Vec has one entry per iteration.
/// The BTreeMap maps each phase to a filename for the dot graph
#[derive(Clone)]
pub struct DotGraphs(Vec<Vec<BTreeMap<DataflowStmtPhase, String>>>);

impl DotGraphs {
    pub fn new() -> Self {
        Self(vec![])
    }

    fn relative_filename(
        &self,
        phase: DataflowStmtPhase,
        block: BasicBlock,
        statement_index: usize,
    ) -> String {
        let iteration = self.num_iterations(statement_index);
        format!(
            "{:?}_stmt_{}_iteration_{}_{}.dot",
            block,
            statement_index,
            iteration,
            phase.to_filename_str_part()
        )
    }

    pub fn register_new_iteration(&mut self, statement_index: usize) {
        if self.0.len() <= statement_index {
            self.0.resize_with(statement_index + 1, Vec::new);
        }
        self.0[statement_index].push(BTreeMap::new());
    }

    pub fn num_iterations(&self, statement_index: usize) -> usize {
        self.0[statement_index].len()
    }

    pub fn insert(&mut self, statement_index: usize, phase: DataflowStmtPhase, filename: String) {
        let top = self.0[statement_index].last_mut().unwrap();
        top.insert(phase, filename);
    }

    pub fn write_json_file(&self, filename: &str) {
        let iterations_json = self
            .0
            .iter()
            .map(|iterations| {
                iterations
                    .into_iter()
                    .map(|map| {
                        map.into_iter()
                            .sorted_by_key(|x| x.0)
                            .map(|(phase, filename)| (format!("{:?}", phase), filename))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        std::fs::write(
            filename,
            serde_json::to_string_pretty(&iterations_json).unwrap(),
        );
    }
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    fn dot_filename_for(
        &self,
        output_dir: &str,
        phase: DataflowStmtPhase,
        statement_index: usize,
    ) -> String {
        format!(
            "{}/{}",
            output_dir,
            self.dot_graphs
                .relative_filename(phase, self.block, statement_index)
        )
    }
    pub fn generate_dot_graph(&mut self, phase: DataflowStmtPhase, statement_index: usize) {
        if let Some(output_dir) = &self.dot_output_dir {
            if phase == DataflowStmtPhase::Initial {
                self.dot_graphs.register_new_iteration(statement_index);
            }
            let relative_filename =
                self.dot_graphs
                    .relative_filename(phase, self.block, statement_index);
            let filename = self.dot_filename_for(&output_dir, phase, statement_index);
            self.dot_graphs
                .insert(statement_index, phase, relative_filename);

            let (fpcs, borrows) = match phase {
                DataflowStmtPhase::Initial | DataflowStmtPhase::BeforeStart => {
                    (&self.fpcs.before_start, &self.borrows.before_start)
                }
                DataflowStmtPhase::BeforeAfter => {
                    (&self.fpcs.before_after, &self.borrows.before_after)
                }
                DataflowStmtPhase::Start => (&self.fpcs.start, &self.borrows.start),
                DataflowStmtPhase::After | DataflowStmtPhase::Join(_) => {
                    (&self.fpcs.after, &self.borrows.after)
                }
            };

            generate_dot_graph(
                self.cgx.rp,
                fpcs,
                borrows,
                self.cgx.mir.borrow_set.as_ref(),
                &filename,
            );
        }
    }

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
            dot_graphs: DotGraphs::new(),
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
        self.dot_graphs.register_new_iteration(0);
        self.generate_dot_graph(DataflowStmtPhase::Join(other.block), 0);
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
