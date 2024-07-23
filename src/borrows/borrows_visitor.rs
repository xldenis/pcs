use std::{borrow::Cow, collections::HashSet, ops::ControlFlow, rc::Rc};

use rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, RegionInferenceContext, RichLocation,
        },
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{Analysis, AnalysisDomain, Forward, JoinSemiLattice},
    index::IndexVec,
    middle::{
        mir::{
            visit::{TyContext, Visitor},
            BasicBlock, Body, CallReturnPlaces, HasLocalDecls, Local, Location, Operand, Place,
            ProjectionElem, Promoted, Rvalue, Statement, StatementKind, Terminator,
            TerminatorEdges, TerminatorKind, VarDebugInfo, RETURN_PLACE, START_BLOCK,
        },
        ty::{self, Region, RegionKind, RegionVid, TyCtxt, TypeVisitor},
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::domain::RegionAbstraction,
    rustc_interface,
    utils::{self, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::domain::{Borrow, DerefExpansion, MaybeOldPlace, Reborrow};
use super::{
    borrows_state::BorrowsState,
    engine::{BorrowsDomain, BorrowsEngine},
};

pub struct BorrowsVisitor<'tcx, 'mir, 'state> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    state: &'state mut BorrowsDomain<'mir, 'tcx>,
    input_facts: &'mir PoloniusInput,
    location_table: &'mir LocationTable,
    borrow_set: Rc<BorrowSet<'tcx>>,
    before: bool,
    preparing: bool,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(self.body, self.tcx)
    }
    pub fn preparing(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, before, true)
    }

    pub fn applying(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, before, false)
    }

    fn new(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
        preparing: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor {
            tcx: engine.tcx,
            body: engine.body,
            state,
            input_facts: engine.input_facts,
            before,
            preparing,
            location_table: engine.location_table,
            borrow_set: engine.borrow_set.clone(),
        }
    }
    fn ensure_expansion_to_exactly(&mut self, place: utils::Place<'tcx>, location: Location) {
        self.state.after.ensure_expansion_to_exactly(
            self.tcx,
            self.body,
            MaybeOldPlace::Current { place },
            location,
        )
    }

    fn loans_invalidated_at(&self, location: Location, start: bool) -> Vec<BorrowIndex> {
        self.input_facts
            .loan_invalidated_at
            .iter()
            .filter_map(
                |(loan_point, loan)| match self.location_table.to_location(*loan_point) {
                    RichLocation::Start(loan_location) if loan_location == location && start => {
                        Some(*loan)
                    }
                    RichLocation::Mid(loan_location) if loan_location == location && !start => {
                        Some(*loan)
                    }
                    _ => None,
                },
            )
            .collect()
    }
}

impl<'tcx, 'mir, 'state> Visitor<'tcx> for BorrowsVisitor<'tcx, 'mir, 'state> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.before && self.preparing {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if place.is_owned(self.body, self.tcx) && place.is_ref(self.body, self.tcx) {
                        self.ensure_expansion_to_exactly(
                            place.project_deref(self.repacker()),
                            location,
                        );
                    } else {
                        self.ensure_expansion_to_exactly(place, location);
                    }
                }
                _ => {}
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if !self.before && !self.preparing {
            match &terminator.kind {
                TerminatorKind::Call { args, .. } => {
                    for arg in args {
                        if let Operand::Move(arg) = arg {
                            self.state.after.remove_loans_assigned_to(
                                self.tcx,
                                &self.borrow_set,
                                (*arg).into(),
                                location.block,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        if self.preparing {
            for loan in self.loans_invalidated_at(location, self.before) {
                self.state.after.remove_rustc_borrow(
                    self.tcx,
                    &loan,
                    &self.borrow_set,
                    &self.body,
                    location.block,
                );
            }
        }

        // Stuff in this block will be included as the middle "bridge" ops that
        // are visible to Prusti
        if self.preparing && !self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, _)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    if !target.is_owned(self.body, self.tcx) {
                        self.ensure_expansion_to_exactly(target, location);
                    }
                }
                StatementKind::StorageDead(local) => {
                    let place: utils::Place<'tcx> = (*local).into();
                    let repacker = PlaceRepacker::new(self.body, self.tcx);
                    if place.ty(repacker).ty.is_ref() {
                        self.state.after.make_place_old(place, repacker);
                    }
                }
                _ => {}
            }
        }

        // Will be included as start bridge ops
        if self.preparing && self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    if target.ty(self.body, self.tcx).ty.is_ref() {
                        let target = (*target).into();
                        self.state.after.make_place_old(
                            target,
                            PlaceRepacker::new(self.body, self.tcx),
                        );
                    }
                }
                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.body, self.tcx) {
                        if place.is_ref(self.body, self.tcx) {
                            self.ensure_expansion_to_exactly(
                                place.project_deref(self.repacker()),
                                location,
                            );
                        } else {
                            self.ensure_expansion_to_exactly(place, location);
                        }
                    }
                }
                _ => {}
            }
        }

        if !self.preparing && !self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    self.state.after.set_latest((*target).into(), location);
                    match rvalue {
                        Rvalue::Use(Operand::Move(from)) => {
                            let from: utils::Place<'tcx> = (*from).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            if matches!(from.ty(self.repacker()).ty.kind(), ty::TyKind::Ref(_, _, r) if r.is_mut())
                            {
                                self.state.after.move_reborrows(
                                    from.project_deref(self.repacker()),
                                    target.project_deref(self.repacker()),
                                );
                            }
                            self.state.after.make_place_old(
                                from,
                                PlaceRepacker::new(self.body, self.tcx),
                            );
                        }
                        Rvalue::Use(Operand::Copy(from)) => {
                            if from.ty(self.body, self.tcx).ty.is_ref() {
                                let from: utils::Place<'tcx> = (*from).into();
                                let target: utils::Place<'tcx> = (*target).into();
                                self.state.after.add_reborrow(
                                    from.project_deref(self.repacker()),
                                    target.project_deref(self.repacker()),
                                    Mutability::Not,
                                    location,
                                )
                            }
                        }
                        Rvalue::Ref(_, kind, blocked_place) => {
                            let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            let assigned_place = target.project_deref(self.repacker());
                            assert_eq!(
                                self.tcx
                                    .erase_regions((*blocked_place).ty(self.body, self.tcx).ty),
                                self.tcx
                                    .erase_regions((*assigned_place).ty(self.body, self.tcx).ty)
                            );
                            self.state.after.add_reborrow(
                                blocked_place,
                                assigned_place,
                                kind.mutability(),
                                location,
                            );
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
        use Rvalue::*;
        match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | CheckedBinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => {}

            &Ref(_, _, place)
            | &AddressOf(_, place)
            | &Len(place)
            | &Discriminant(place)
            | &CopyForDeref(place) => {
                let place: utils::Place<'tcx> = place.into();
                if self.before && self.preparing && !place.is_owned(self.body, self.tcx) {
                    self.ensure_expansion_to_exactly(place, location);
                }
            }
        }
    }
}
