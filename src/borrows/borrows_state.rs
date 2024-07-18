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
use serde_json::{json, Value};

use crate::{
    borrows::unblock_reason::{UnblockReason, UnblockReasons},
    combined_pcs::UnblockGraph,
    free_pcs::CapabilityProjections,
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::{
    deref_expansions::DerefExpansions,
    domain::{Borrow, DerefExpansion, Latest, MaybeOldPlace, Reborrow, RegionAbstraction},
    reborrowing_dag::ReborrowingDag,
};

impl<'mir, 'tcx> JoinSemiLattice for BorrowsState<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        eprintln!("JOIN");
        let mut changed = false;
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
        if self.latest.join(&other.latest, self.body) {
            changed = true;
        }
        changed
    }
}

#[derive(Clone, Debug)]
pub struct BorrowsState<'mir, 'tcx> {
    body: &'mir mir::Body<'tcx>,
    latest: Latest<'tcx>,
    pub reborrows: ReborrowingDag<'tcx>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
    pub deref_expansions: DerefExpansions<'tcx>,
    pub logs: Vec<String>,
}

impl<'mir, 'tcx> PartialEq for BorrowsState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.reborrows == other.reborrows
            && self.deref_expansions == other.deref_expansions
            && self.latest == other.latest
    }
}

impl<'mir, 'tcx> Eq for BorrowsState<'mir, 'tcx> {}

impl<'mir, 'tcx> BorrowsState<'mir, 'tcx> {
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
                    UnblockReasons::new(UnblockReason::NotInStateToBridge(reborrow.clone())),
                );
            }
        }

        for exp in self.deref_expansions.iter() {
            if !to
                .deref_expansions
                .has_expansion_at_location(exp.base.place(), exp.location)
            {
                ug.unblock_place(
                    exp.base,
                    self,
                    exp.location.block,
                    UnblockReasons::new(UnblockReason::DerefExpansionDoesntExist(
                        exp.base.place(),
                        exp.location,
                    )),
                );
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

    pub fn remove_dangling_old_places(&mut self) {
        while self.remove_dangling_old_places_pass() {
            eprintln!("Iteration");
        }
    }

    pub fn is_leaf(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.reborrows.get_places_blocking(place).is_empty()
            && !self.deref_expansions.contains_expansion_from(place)
    }

    pub fn leaves(&self) -> (FxHashSet<&Reborrow<'tcx>>, FxHashSet<&DerefExpansion<'tcx>>) {
        let mut reborrows: FxHashSet<_> = self.reborrows.iter().collect();
        let mut deref_expansions: FxHashSet<_> = self.deref_expansions.iter().collect();
        reborrows.retain(|rb| self.is_leaf(rb.assigned_place));
        deref_expansions.retain(|de| de.expansion().iter().all(|e| self.is_leaf(*e)));
        return (reborrows, deref_expansions);
    }

    // TODO: This is not precise, consider each location separately
    pub fn remove_dangling_old_places_pass(&mut self) -> bool {
        let mut changed = false;
        let (reborrows, deref_expansions) = self.leaves();
        let mut reborrows = reborrows
            .into_iter()
            .cloned()
            .collect::<FxHashSet<Reborrow<'tcx>>>();
        let mut deref_expansions = deref_expansions
            .into_iter()
            .cloned()
            .collect::<FxHashSet<DerefExpansion<'tcx>>>();
        for rb in reborrows {
            if !rb.assigned_place.is_current() {
                if self.reborrows.remove(&rb) {
                    changed = true;
                }
            }
        }
        for de in deref_expansions {
            if !de.base.is_current() {
                if self.deref_expansions.remove(&de) {
                    changed = true;
                }
            }
        }
        changed
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
                    if self.reborrows.kill_reborrows(blocked_place, assigned_place) {
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

    pub fn reborrows(&self) -> &ReborrowingDag<'tcx> {
        &self.reborrows
    }

    pub fn set_latest(&mut self, place: Place<'tcx>, location: Location) {
        self.latest.insert(place, location);
    }

    pub fn get_latest(&self, place: &Place<'tcx>) -> Location {
        self.latest.get(place)
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

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: Place<'tcx>,
        new_assigned_place: Place<'tcx>,
    ) {
        self.reborrows.move_reborrows(
            MaybeOldPlace::Current {
                place: orig_assigned_place,
            },
            MaybeOldPlace::Current {
                place: new_assigned_place,
            },
        );
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
        json!({})
    }

    pub fn new(body: &'mir mir::Body<'tcx>) -> Self {
        Self {
            body,
            deref_expansions: DerefExpansions::new(),
            latest: Latest::new(),
            reborrows: ReborrowingDag::new(),
            region_abstractions: vec![],
            logs: vec![],
        }
    }

    fn log(&mut self, log: String) {
        self.logs.push(log);
    }

    pub fn is_current(&self, place: &PlaceSnapshot<'tcx>, body: &mir::Body<'tcx>) -> bool {
        let last_loc = self.latest.get(&place.place);
        let result = if last_loc.block == place.at.block {
            last_loc.statement_index <= place.at.statement_index
        } else {
            body.basic_blocks
                .dominators()
                .dominates(last_loc.block, place.at.block)
        };
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

    pub fn make_deref_of_place_old(
        &mut self,
        place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        let location = self.get_latest(&place);
        self.reborrows
            .make_place_old(place.project_deref(repacker), location);
        self.deref_expansions.make_place_old(place, location);
        self.remove_dangling_old_places();
    }

    pub fn remove_borrow(&mut self, tcx: TyCtxt<'tcx>, borrow: &Borrow<'tcx>, block: BasicBlock) {
        let mut g = UnblockGraph::new();

        // TODO: old places
        g.unblock_place(
            MaybeOldPlace::Current {
                place: borrow.borrowed_place,
            },
            &self,
            block,
            UnblockReasons::new(UnblockReason::RemoveBorrow(borrow.clone())),
        );

        self.apply_unblock_graph(g);
    }

    pub fn remove_rustc_borrow(
        &mut self,
        tcx: TyCtxt<'tcx>,
        rustc_borrow: &BorrowIndex,
        borrow_set: &BorrowSet<'tcx>,
        body: &mir::Body<'tcx>,
        block: BasicBlock,
    ) {
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
    ) {
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
    }
}
