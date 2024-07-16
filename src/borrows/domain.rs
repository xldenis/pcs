use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::{
        fx::{FxHashMap, FxHashSet},
        graph::dominators::Dominators,
    },
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Local, Location, VarDebugInfo},
    middle::ty::TyCtxt,
};

use crate::{
    combined_pcs::UnblockGraph, free_pcs::CapabilityProjections, rustc_interface, utils::Place,
    ReborrowBridge,
};

impl<'mir, 'tcx> JoinSemiLattice for BorrowsState<'mir, 'tcx> {
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
        if self.latest.join(&other.latest) {
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
    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceSnapshot<'tcx> {
        PlaceSnapshot {
            place: self.place.project_deref(repacker),
            at: self.at,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current {
            place: place.into(),
        }
    }
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn new(place: Place<'tcx>, at: Option<Location>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot { place, at })
        } else {
            Self::Current { place }
        }
    }

    pub fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.ty(repacker),
            MaybeOldPlace::OldPlace(old_place) => old_place.place.ty(repacker),
        }
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => MaybeOldPlace::Current {
                place: place.project_deref(repacker),
            },
            MaybeOldPlace::OldPlace(old_place) => {
                MaybeOldPlace::OldPlace(old_place.project_deref(repacker))
            }
        }
    }

    pub fn is_mut_ref(&self, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        self.place().is_mut_ref(body, tcx)
    }

    pub fn is_ref(&self, body: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        self.place().is_ref(body, tcx)
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

    pub fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let p = self.place().to_short_string(repacker);
        format!(
            "{}{}",
            p,
            if let Some(location) = self.location() {
                format!(" at {:?}", location)
            } else {
                "".to_string()
            }
        )
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Borrow<'tcx> {
    pub borrowed_place: Place<'tcx>,
    pub assigned_place: Place<'tcx>,
    pub is_mut: bool,
}

impl<'tcx> Borrow<'tcx> {
    pub fn new(borrowed_place: Place<'tcx>, assigned_place: Place<'tcx>, is_mut: bool) -> Self {
        Self {
            borrowed_place,
            assigned_place,
            is_mut,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "borrowed_place": self.borrowed_place.to_json(repacker),
            "assigned_place": self.assigned_place.to_json(repacker),
            "is_mut": self.is_mut,
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct DerefExpansion<'tcx> {
    pub base: MaybeOldPlace<'tcx>,
    pub expansion: Vec<Place<'tcx>>,
    pub location: Location,
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn new(base: MaybeOldPlace<'tcx>, expansion: Vec<Place<'tcx>>, location: Location) -> Self {
        Self {
            base,
            expansion,
            location,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(repacker),
            "expansion": self.expansion.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

#[derive(Clone, Debug)]
struct Latest<'mir, 'tcx>(FxHashMap<Place<'tcx>, Location>, &'mir mir::Body<'tcx>);

impl<'mir, 'tcx> PartialEq for Latest<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<'mir, 'tcx> Eq for Latest<'mir, 'tcx> {}

impl<'mir, 'tcx> Latest<'mir, 'tcx> {
    pub fn new(body: &'mir mir::Body<'tcx>) -> Self {
        Self(FxHashMap::default(), body)
    }
    pub fn get(&self, place: &Place<'tcx>) -> Option<&Location> {
        self.0.get(place)
    }
    pub fn insert(&mut self, place: Place<'tcx>, location: Location) -> Option<Location> {
        self.0.insert(place, location)
    }
}

fn join_locations(loc1: Location, loc2: Location, dominators: &Dominators<BasicBlock>) -> Location {
    if loc1.dominates(loc2, dominators) {
        loc1
    } else if loc2.dominates(loc1, dominators) {
        loc2
    } else {
        for block in dominators.dominators(loc2.block) {
            if dominators.dominates(block, loc1.block) {
                return Location {
                    block,
                    statement_index: 0,
                };
            }
        }
        unreachable!()
    }
}

impl<'mir, 'tcx> JoinSemiLattice for Latest<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (place, other_loc) in other.0.iter() {
            if let Some(self_loc) = self.get(place) {
                let dominators = self.1.basic_blocks.dominators();
                let new_loc = join_locations(*self_loc, *other_loc, dominators);
                if new_loc != *self_loc {
                    self.insert(*place, new_loc);
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsState<'mir, 'tcx> {
    latest: Latest<'mir, 'tcx>,
    pub reborrows: ReborrowingDag<'tcx>,
    borrows: FxHashSet<Borrow<'tcx>>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
    pub deref_expansions: DerefExpansions<'tcx>,
    pub logs: Vec<String>,
}

use crate::utils::PlaceRepacker;
use serde_json::{json, Value};

use super::{
    deref_expansions::DerefExpansions, engine::ReborrowAction, reborrowing_dag::ReborrowingDag,
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

impl<'mir, 'tcx> BorrowsState<'mir, 'tcx> {
    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.reborrows.filter_for_path(path);
    }
    pub fn bridge(&self, to: &Self, block: BasicBlock) -> ReborrowBridge<'tcx> {
        let added_reborrows: FxHashSet<Reborrow<'tcx>> = to
            .reborrows()
            .iter()
            .filter(|rb| {
                !self.has_reborrow_at_location(
                    rb.blocked_place.place(),
                    rb.assigned_place.place(),
                    rb.location,
                )
            })
            .cloned()
            .collect();
        let expands: FxHashSet<DerefExpansion<'tcx>> = to
            .deref_expansions
            .iter()
            .filter(|exp| {
                !self
                    .deref_expansions
                    .has_expansion_at_location(exp.base.place(), exp.location)
            })
            .cloned()
            .collect();

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows().iter() {
            if !to.has_reborrow_at_location(
                reborrow.blocked_place.place(),
                reborrow.assigned_place.place(),
                reborrow.location,
            ) {
                ug.kill_reborrow(
                    *reborrow,
                    self,
                    "it doesn't exist in state to bridge".to_string(),
                );
            }
        }

        for exp in self.deref_expansions.iter() {
            if !to
                .deref_expansions
                .has_expansion_at_location(exp.base.place(), exp.location)
            {
                ug.unblock_place(exp.base, self, exp.location.block);
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
        location: Location,
    ) {
        self.deref_expansions
            .ensure_expansion_to(place, body, tcx, location);
    }

    pub fn roots_of(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<MaybeOldPlace<'tcx>> {
        let mut result = FxHashSet::default();
        for place in self.reborrows.get_places_blocking(place) {
            result.extend(self.roots_of(place));
        }
        for place in self.deref_expansions.get_parents(place) {
            result.extend(self.roots_of(place));
        }
        if result.is_empty() {
            result.insert(place);
        }
        result
    }

    // TODO: This is not precise, consider each location separately
    pub fn trim_roots(&mut self) {
        let roots: FxHashSet<_> = self
            .reborrows
            .roots()
            .into_iter()
            .flat_map(|place| self.roots_of(place))
            .flat_map(|place| match place {
                MaybeOldPlace::OldPlace(place) => Some(place),
                _ => None,
            })
            .collect();
        for root in roots {
            // TODO: deref expansions
            self.reborrows
                .kill_reborrows_assigned_to(MaybeOldPlace::OldPlace(root));
        }
    }

    /// Returns places in the PCS that are reborrowed
    pub fn reborrow_roots(&self) -> FxHashSet<Place<'tcx>> {
        self.reborrows
            .roots()
            .into_iter()
            .flat_map(|place| self.roots_of(place))
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
                    if self.reborrows.kill_reborrow(blocked_place, assigned_place) {
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
        self.latest.insert(place, location);
    }

    pub fn get_latest(&self, place: &Place<'tcx>) -> Option<Location> {
        self.latest.get(place).cloned()
    }

    pub fn reborrows_blocking(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<&Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|rb| rb.blocked_place == place)
            .collect()
    }

    pub fn reborrows_assigned_to(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<&Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|rb| rb.assigned_place == place)
            .collect()
    }

    pub fn kill_reborrows_blocking(&mut self, place: MaybeOldPlace<'tcx>) {
        self.reborrows.kill_reborrows_blocking(place);
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

    pub fn has_reborrow_at_location(
        &self,
        from: Place<'tcx>,
        to: Place<'tcx>,
        location: Location,
    ) -> bool {
        self.reborrows.has_reborrow_at_location(from, to, location)
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({
            "borrows": self.borrows.iter().map(|borrow| {
                borrow.to_json(repacker)
            }).collect::<Vec<_>>(),
        })
    }

    pub fn new(body: &'mir mir::Body<'tcx>) -> Self {
        Self {
            deref_expansions: DerefExpansions::new(),
            latest: Latest::new(body),
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

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        if !self.region_abstractions.contains(&abstraction) {
            self.region_abstractions.push(abstraction);
        }
    }

    pub fn add_borrow(&mut self, tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, borrow: Borrow<'tcx>) {
        let assigned_place = borrow.assigned_place;
        let deref_of_assigned_place = assigned_place.project_deref(PlaceRepacker::new(body, tcx));
        // self.borrows.insert(borrow);
    }

    pub fn make_deref_of_place_old(
        &mut self,
        place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        if let Some(location) = self.get_latest(&place) {
            self.reborrows
                .make_place_old(place.project_deref(repacker), location);
            self.deref_expansions
                .make_place_old(place.project_deref(repacker), location);
            self.trim_roots();
        }
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
                borrow_set[borrow].borrowed_place.into(),
                borrow_set[borrow].assigned_place.into(),
                matches!(borrow_set[borrow].kind, mir::BorrowKind::Mut { .. }),
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
        borrow_set: &BorrowSet<'tcx>,
        body: &mir::Body<'tcx>,
        block: BasicBlock,
    ) -> bool {
        let borrow = &borrow_set[*rustc_borrow];
        let borrow = Borrow::new(
            borrow.borrowed_place.into(),
            borrow.assigned_place.into(),
            matches!(borrow.kind, mir::BorrowKind::Mut { .. }),
        );
        self.remove_borrow(tcx, &borrow, block)
    }
    pub fn remove_loans_assigned_to(
        &mut self,
        tcx: TyCtxt<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        place: Place<'tcx>,
        block: BasicBlock,
    ) -> FxHashSet<Borrow<'tcx>> {
        for (idx, borrow) in borrow_set.location_map.iter() {
            let assigned_place: Place<'tcx> = borrow.assigned_place.into();
            if assigned_place == place {
                self.remove_borrow(
                    tcx,
                    &Borrow::new(
                        borrow.borrowed_place.into(),
                        borrow.assigned_place.into(),
                        matches!(borrow.kind, mir::BorrowKind::Mut { .. }),
                    ),
                    block,
                );
            }
        }
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
