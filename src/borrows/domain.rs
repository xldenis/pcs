use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, BasicBlock, Local, Location, VarDebugInfo},
    middle::ty::TyCtxt,
};

use crate::{
    combined_pcs::UnblockGraph, free_pcs::CapabilityProjections, rustc_interface, utils::Place,
    ReborrowBridge,
};

impl<'tcx> JoinSemiLattice for BorrowsState<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for borrow in &other.borrows {
            if self.borrows.insert(borrow.clone()) {
                changed = true;
            }
        }
        for region_abstraction in &other.region_abstractions {
            if !self.region_abstractions.contains(region_abstraction) {
                self.region_abstractions.push(region_abstraction.clone());
                changed = true;
            }
        }
        for reborrow in other.reborrows.iter() {
            if self.reborrows.insert(reborrow.clone()) {
                changed = true;
            }
        }
        if self.deref_expansions.join(&other.deref_expansions) {
            changed = true;
        }
        changed
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RegionAbstraction<'tcx> {
    pub loans_in: FxHashSet<mir::Place<'tcx>>,
    pub loans_out: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> RegionAbstraction<'tcx> {
    pub fn new() -> Self {
        Self {
            loans_in: FxHashSet::default(),
            loans_out: FxHashSet::default(),
        }
    }

    pub fn add_loan_in(&mut self, loan: mir::Place<'tcx>) {
        self.loans_in.insert(loan);
    }

    pub fn add_loan_out(&mut self, loan: mir::Place<'tcx>) {
        self.loans_out.insert(loan);
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct PlaceSnapshot<'tcx> {
    pub place: Place<'tcx>,
    pub at: Location,
}

impl<'tcx> PlaceSnapshot<'tcx> {
    pub fn project_deref(&self, tcx: TyCtxt<'tcx>) -> PlaceSnapshot<'tcx> {
        PlaceSnapshot {
            place: self.place.project_deref(tcx),
            at: self.at,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn new(place: Place<'tcx>, at: Option<Location>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot { place, at })
        } else {
            Self::Current { place }
        }
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace(old_place) => old_place.place,
        }
    }

    pub fn location(&self) -> Option<Location> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.at),
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{:?}", loc)),
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Borrow<'tcx> {
    pub index: BorrowIndex,
    pub borrowed_place: Place<'tcx>,
    pub assigned_place: Place<'tcx>,
    pub is_mut: bool,
    pub location: Location,
}

impl<'tcx> Borrow<'tcx> {
    pub fn new(
        index: BorrowIndex,
        borrowed_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        is_mut: bool,
        location: Location,
    ) -> Self {
        Self {
            index,
            borrowed_place,
            assigned_place,
            is_mut,
            location,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "index": format!("{:?}", self.index),
            "borrowed_place": self.borrowed_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "location": format!("{:?}", self.location),
            "is_mut": self.is_mut,
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct DerefExpansion<'tcx> {
    pub base: MaybeOldPlace<'tcx>,
    pub expansion: Vec<Place<'tcx>>,
    pub block: BasicBlock,
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn new(base: MaybeOldPlace<'tcx>, expansion: Vec<Place<'tcx>>, block: BasicBlock) -> Self {
        Self {
            base,
            expansion,
            block,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(repacker),
            "expansion": self.expansion.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsState<'tcx> {
    latest: FxHashMap<Place<'tcx>, Location>,
    pub reborrows: ReborrowingDag<'tcx>,
    borrows: FxHashSet<Borrow<'tcx>>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
    pub deref_expansions: DerefExpansions<'tcx>,
    pub logs: Vec<String>,
}

use crate::utils::PlaceRepacker;
use serde_json::{json, Value};

use super::{
    deref_expansions::DerefExpansions,
    engine::{BorrowAction, ReborrowAction},
    reborrowing_dag::ReborrowingDag,
};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct Reborrow<'tcx> {
    pub blocked_place: MaybeOldPlace<'tcx>,
    pub assigned_place: MaybeOldPlace<'tcx>,
    pub mutability: Mutability,

    /// The location when the reborrow was created
    pub location: Location,
}

impl<'tcx> Reborrow<'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "blocked_place": self.blocked_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.mutability == Mutability::Mut
        })
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.reborrows.filter_for_path(path);
    }
    pub fn bridge(&self, to: &Self, block: BasicBlock) -> ReborrowBridge<'tcx> {
        let added_reborrows: FxHashSet<Reborrow<'tcx>> = to
            .reborrows()
            .iter()
            .filter(|rb| !self.contains_reborrow(rb))
            .cloned()
            .collect();
        let expands: FxHashSet<DerefExpansion<'tcx>> = to
            .deref_expansions
            .iter()
            .filter(|exp| !self.deref_expansions.contains(exp))
            .cloned()
            .collect();

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows().iter() {
            if !to.contains_reborrow(reborrow) {
                ug.unblock_reborrow(*reborrow, self)
            }
        }

        for exp in self.deref_expansions.iter() {
            if !to.deref_expansions.contains(&exp) {
                ug.unblock_place(exp.base, self, block);
            }
        }

        ReborrowBridge {
            added_reborrows,
            expands,
            ug,
        }
    }
    pub fn ensure_expansion_to(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: MaybeOldPlace<'tcx>,
        block: BasicBlock,
    ) {
        self.deref_expansions
            .ensure_expansion_to(place, body, tcx, block);
    }

    pub fn root_of(&self, place: MaybeOldPlace<'tcx>) -> MaybeOldPlace<'tcx> {
        if let Some(place) = self.reborrows.get_place_blocking(place) {
            self.root_of(place)
        } else if let Some(place) = self.deref_expansions.get_parent(place) {
            self.root_of(place)
        } else {
            place
        }
    }

    /// Returns places in the PCS that are reborrowed
    pub fn reborrow_roots(&self) -> FxHashSet<Place<'tcx>> {
        self.reborrows
            .roots()
            .into_iter()
            .map(|place| self.root_of(place))
            .flat_map(|place| match place {
                MaybeOldPlace::Current { place } => Some(place),
                MaybeOldPlace::OldPlace(_) => None,
            })
            .collect()
    }

    pub fn apply_unblock_graph(&mut self, graph: UnblockGraph<'tcx>) -> bool {
        let mut changed = false;
        for action in graph.actions() {
            match action {
                crate::combined_pcs::UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    ..
                } => {
                    if self
                        .reborrows
                        .kill_reborrow_blocking(blocked_place)
                        .is_some()
                    {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.deref_expansions.delete_descendants_of(place) {
                        changed = true;
                    }
                }
            }
        }
        changed
    }

    pub fn borrows(&self) -> &FxHashSet<Borrow<'tcx>> {
        &self.borrows
    }

    pub fn reborrows(&self) -> &ReborrowingDag<'tcx> {
        &self.reborrows
    }

    pub fn set_latest(&mut self, place: Place<'tcx>, location: Location) {
        if let Some(old_location) = self.latest.insert(place, location) {
            eprintln!("{:?}: {:?} -> {:?}", place, old_location, location);
        }
    }

    pub fn get_latest(&self, place: &Place<'tcx>) -> Option<Location> {
        self.latest.get(place).cloned()
    }

    pub fn find_reborrow_blocking(&self, place: MaybeOldPlace<'tcx>) -> Option<&Reborrow<'tcx>> {
        self.reborrows.iter().find(|rb| rb.blocked_place == place)
    }

    pub fn kill_reborrow_blocking(&mut self, place: MaybeOldPlace<'tcx>) {
        self.reborrows.kill_reborrow_blocking(place);
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
    ) {
        self.reborrows
            .add_reborrow(blocked_place, assigned_place, mutability, location);
        self.log("Add reborrow".to_string());
    }

    pub fn contains_reborrow(&self, reborrow: &Reborrow<'tcx>) -> bool {
        self.reborrows.contains(reborrow)
    }

    pub fn contains_borrow(&self, borrow: &Borrow<'tcx>) -> bool {
        self.borrows.contains(borrow)
    }

    pub fn apply_action(&mut self, action: BorrowAction<'_, 'tcx>) {
        match action {
            BorrowAction::AddBorrow(borrow) => self.borrows.insert(borrow.into_owned()),
            BorrowAction::RemoveBorrow(borrow) => self.borrows.remove(borrow),
        };
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({
            "borrows": self.borrows.iter().map(|borrow| {
                borrow.to_json(repacker)
            }).collect::<Vec<_>>(),
        })
    }

    pub fn new() -> Self {
        Self {
            deref_expansions: DerefExpansions::new(),
            latest: FxHashMap::default(),
            reborrows: ReborrowingDag::new(),
            borrows: FxHashSet::default(),
            region_abstractions: vec![],
            logs: vec![],
        }
    }

    fn log(&mut self, log: String) {
        self.logs.push(log);
    }

    pub fn is_current(&self, place: &PlaceSnapshot<'tcx>, body: &mir::Body<'tcx>) -> bool {
        let result = self.latest.get(&place.place).map_or(true, |loc| {
            if loc.block == place.at.block {
                loc.statement_index <= place.at.statement_index
            } else {
                body.basic_blocks
                    .dominators()
                    .dominates(loc.block, place.at.block)
            }
        });
        if !result {
            eprintln!(
                "is_current({:?}) = {:?} <{:?}>",
                place,
                result,
                self.latest.get(&place.place)
            );
        }
        result
    }

    // pub fn place_loaned_to_place(
    //     &self,
    //     place: Place<'tcx>,
    //     body: &mir::Body<'tcx>,
    // ) -> Option<PlaceSnapshot<'tcx>> {
    //     self.live_borrows(body)
    //         .iter()
    //         .find(|borrow| borrow.assigned_place == place)
    //         .map(|borrow| borrow.borrowed_place)
    // }

    // pub fn reference_targeting_place(
    //     &self,
    //     place: Place<'tcx>,
    //     borrow_set: &BorrowSet<'tcx>,
    //     body: &mir::Body<'tcx>,
    // ) -> Option<Place<'tcx>> {
    //     self.live_borrows(body)
    //         .iter()
    //         .find(|borrow| borrow.borrowed_place == place)
    //         .map(|borrow| borrow.assigned_place)
    // }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        if !self.region_abstractions.contains(&abstraction) {
            self.region_abstractions.push(abstraction);
        }
    }

    pub fn add_borrow(&mut self, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, borrow: Borrow<'tcx>) {
        let assigned_place = borrow.assigned_place;
        let deref_of_assigned_place = assigned_place.project_deref(tcx);
        self.borrows.insert(borrow);
    }

    pub fn add_rustc_borrow(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        borrow: BorrowIndex,
        borrow_set: &BorrowSet<'tcx>,
        location: Location,
    ) {
        self.add_borrow(
            tcx,
            body,
            Borrow::new(
                borrow,
                borrow_set[borrow].borrowed_place.into(),
                borrow_set[borrow].assigned_place.into(),
                matches!(borrow_set[borrow].kind, mir::BorrowKind::Mut { .. }),
                location,
            ),
        );
    }

    pub fn remove_borrow(
        &mut self,
        tcx: TyCtxt<'tcx>,
        borrow: &Borrow<'tcx>,
        block: BasicBlock,
    ) -> bool {
        let mut g = UnblockGraph::new();

        // TODO: old places
        g.unblock_place(
            MaybeOldPlace::Current {
                place: borrow.borrowed_place,
            },
            &self,
            block,
        );

        self.apply_unblock_graph(g);

        self.borrows.remove(&borrow.clone())
    }

    pub fn remove_rustc_borrow(
        &mut self,
        tcx: TyCtxt<'tcx>,
        rustc_borrow: &BorrowIndex,
        body: &mir::Body<'tcx>,
        block: BasicBlock,
    ) -> bool {
        let borrow = self.borrows.iter().find(|b| b.index == *rustc_borrow);
        if let Some(borrow) = borrow {
            self.remove_borrow(tcx, &borrow.clone(), block)
        } else {
            false
        }
    }
    pub fn remove_loans_assigned_to(
        &mut self,
        tcx: TyCtxt<'tcx>,
        place: Place<'tcx>,
        block: BasicBlock,
    ) -> FxHashSet<Borrow<'tcx>> {
        let (to_remove, to_keep): (FxHashSet<_>, FxHashSet<_>) = self
            .borrows
            .clone()
            .into_iter()
            .partition(|borrow| borrow.assigned_place == place);

        self.borrows = to_keep;

        for borrow in to_remove.iter() {
            self.remove_borrow(tcx, borrow, block);
        }

        to_remove
    }
}
