// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{cell::Cell, rc::Rc};

use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{self, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
    },
    dataflow::{Analysis, AnalysisDomain},
    index::{Idx, IndexVec},
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Promoted, Rvalue,
            Statement, StatementKind, Terminator, TerminatorEdges, RETURN_PLACE, START_BLOCK,
        },
        ty::TyCtxt,
    },
};

use crate::{
    borrows::{
        domain::{BorrowsState, MaybeOldPlace, Reborrow},
        engine::{BorrowsEngine, ReborrowAction},
    },
    free_pcs::{
        engine::FpcsEngine, CapabilityKind, CapabilityLocal, CapabilitySummary,
        FreePlaceCapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceOrdering, PlaceRepacker},
};

use super::domain::PlaceCapabilitySummary;

pub struct BodyWithBorrowckFacts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub location_table: Option<Rc<LocationTable>>,
    pub input_facts: Option<Box<PoloniusInput>>,
    pub output_facts: Option<Rc<PoloniusOutput>>,
}

impl<'tcx> From<consumers::BodyWithBorrowckFacts<'tcx>> for BodyWithBorrowckFacts<'tcx> {
    fn from(value: consumers::BodyWithBorrowckFacts<'tcx>) -> Self {
        Self {
            body: value.body,
            promoted: value.promoted,
            borrow_set: value.borrow_set,
            region_inference_context: value.region_inference_context,
            location_table: value.location_table.map(Rc::new),
            input_facts: value.input_facts,
            output_facts: value.output_facts,
        }
    }
}

pub struct PcsContext<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub mir: &'a BodyWithBorrowckFacts<'tcx>,
}

impl<'a, 'tcx> PcsContext<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, mir: &'a BodyWithBorrowckFacts<'tcx>) -> Self {
        let rp = PlaceRepacker::new(&mir.body, &mir.promoted, tcx);
        Self { rp, mir }
    }
}

pub struct PcsEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<PcsContext<'a, 'tcx>>,
    block: Cell<BasicBlock>,

    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) borrows: BorrowsEngine<'a, 'tcx>,
}
impl<'a, 'tcx> PcsEngine<'a, 'tcx> {
    pub fn new(cgx: PcsContext<'a, 'tcx>) -> Self {
        let cgx = Rc::new(cgx);
        let fpcs = FpcsEngine(cgx.rp);
        let borrows = BorrowsEngine::new(
            cgx.rp.tcx(),
            cgx.rp.body(),
            cgx.mir.location_table.as_ref().unwrap(),
            cgx.mir.input_facts.as_ref().unwrap(),
            cgx.mir.borrow_set.clone(),
            cgx.mir.region_inference_context.clone(),
        );
        Self {
            cgx,
            block: Cell::new(START_BLOCK),
            fpcs,
            borrows
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for PcsEngine<'a, 'tcx> {
    type Domain = PlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        let block = self.block.get();
        self.block.set(block.plus(1));
        PlaceCapabilitySummary::new(self.cgx.clone(), block)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.block.set(START_BLOCK);
        state.fpcs.initialize_as_start_block();
        // Initialize borrows if needed
    }
}

#[derive(Clone)]
pub enum UnblockTree<'tcx> {
    Reborrow(Reborrow<'tcx>, Option<Box<UnblockTree<'tcx>>>),
    Collapse(Place<'tcx>, Vec<UnblockTree<'tcx>>),
}

impl<'tcx> UnblockTree<'tcx> {

    pub fn root_place(&self) -> MaybeOldPlace<'tcx> {
        match self {
            UnblockTree::Reborrow(reborrow, _) => reborrow.blocked_place,
            UnblockTree::Collapse(place, _) => MaybeOldPlace::Current { place: *place },
        }
    }

    fn places_blocking_collapse(
        place: Place<'tcx>,
        state: &CapabilitySummary<'tcx>,
    ) -> Vec<Place<'tcx>> {
        match &state[place.local] {
            CapabilityLocal::Unallocated => vec![],
            CapabilityLocal::Allocated(cap) => {
                let related = cap.find_all_related(place, None);
                match related.relation {
                    PlaceOrdering::Prefix => vec![],
                    PlaceOrdering::Equal => vec![],
                    PlaceOrdering::Suffix => related.from.into_iter().map(|p| p.0).collect(),
                    PlaceOrdering::Both => todo!(),
                }
            }
        }
    }

    fn unblock_place<'a>(place: Place<'tcx>, borrows: &BorrowsState<'tcx>, fpcs: &CapabilitySummary<'tcx>) -> Self {
        if let Some(reborrow) = borrows
            .find_reborrow_blocking(MaybeOldPlace::Current { place })
        {
            UnblockTree::unblock_reborrow(reborrow.clone(), borrows, fpcs)
        } else {
            eprintln!("A1");
            UnblockTree::Collapse(
                place,
                UnblockTree::places_blocking_collapse(place, fpcs)
                    .into_iter()
                    .map(|p| UnblockTree::unblock_place(p, borrows, fpcs))
                    .collect(),
            )
        }
    }
    pub fn unblock_reborrow<'a>(
        reborrow: Reborrow<'tcx>,
        borrows: &BorrowsState<'tcx>,
        fpcs: &CapabilitySummary<'tcx>,
    ) -> Self {
        let subtree = if let Some(next) = borrows
            .find_reborrow_blocking(reborrow.assigned_place)
        {
            Some(Box::new(UnblockTree::unblock_reborrow(*next, borrows, fpcs)))
        } else {
            match reborrow.assigned_place {
                MaybeOldPlace::Current { place } => {
                    Some(Box::new(UnblockTree::unblock_place(place, borrows, fpcs)))
                }
                MaybeOldPlace::OldPlace(_) => None,
            }
        };
        UnblockTree::Reborrow(reborrow, subtree)
    }
}

impl<'a, 'tcx> PcsEngine<'a, 'tcx> {
    fn apply_reborrow_actions_to_fpcs<'state>(
        &self,
        state: &'state mut CapabilitySummary<'tcx>,
        actions: Vec<ReborrowAction<'tcx>>,
    ) {
        for action in actions {
            match action {
                ReborrowAction::AddReborrow(_) => {}
                ReborrowAction::RemoveReborrow(bw) => match bw.assigned_place {
                    MaybeOldPlace::Current { place, .. } => {
                        if let CapabilityLocal::Allocated(cap) = &mut state[place.local] {
                            let related = cap.find_all_related(place, None);
                            // todo!("Found {related:?} for {place:?}");
                            if related.relation == PlaceOrdering::Suffix {
                                cap.collapse(related.get_from(), place, self.cgx.rp);
                            }
                        }
                    }
                    _ => {}
                },
            }
        }
    }
}

impl<'a, 'tcx> Analysis<'tcx> for PcsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        // match &statement.kind {
        //     StatementKind::Assign(box (place, Rvalue::Use(operand))) if let Some(place) = operand.place() => {
        //         if let Some(place) = state.borrows.after.reference_targeting_place(place.into(), self.cgx.mir.borrow_set.as_ref(), &self.cgx.mir.body) {
        //             if let CapabilityLocal::Allocated(cap) = &mut state.fpcs.after[place.local] {
        //                 let related = cap.find_all_related(place, Some(crate::utils::PlaceOrdering::Suffix));
        //                 cap.collapse(related.get_from(), place, self.cgx.rp);
        //             }
        //         }
        //     }
        //     _ => {}
        // }
        self.borrows
            .apply_before_statement_effect(&mut state.borrows, statement, location);
        let reborrow_actions = state.borrows.reborrow_actions(true);
        if reborrow_actions.len() > 0 {
            eprintln!(
                "{} reborrow actions at {location:?}",
                reborrow_actions.len()
            );
            eprintln!("{:?}", reborrow_actions);
            eprintln!("{:?}", state.borrows.start.logs);
            // self.apply_reborrow_actions_to_fpcs(&mut state.fpcs.after, reborrow_actions);
        }
        self.fpcs
            .apply_before_statement_effect(&mut state.fpcs, statement, location);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.borrows
            .apply_statement_effect(&mut state.borrows, statement, location);
        let reborrow_actions = state.borrows.reborrow_actions(false);
        if reborrow_actions.len() > 0 {
            eprintln!(
                "{} reborrow actions at {location:?} (after)",
                reborrow_actions.len()
            );
            // self.apply_reborrow_actions_to_fpcs(&mut state.fpcs.after, reborrow_actions);
        }
        self.fpcs
            .apply_statement_effect(&mut state.fpcs, statement, location);
    }
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        self.borrows
            .apply_before_terminator_effect(&mut state.borrows, terminator, location);
        self.fpcs
            .apply_before_terminator_effect(&mut state.fpcs, terminator, location);
    }
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.borrows
            .apply_terminator_effect(&mut state.borrows, terminator, location);
        self.fpcs
            .apply_terminator_effect(&mut state.fpcs, terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}
