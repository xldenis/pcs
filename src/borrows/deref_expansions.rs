use std::rc::Rc;

use crate::{
    rustc_interface::{
        ast::Mutability,
        borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
        data_structures::fx::{FxHashMap, FxHashSet},
        dataflow::{AnalysisDomain, JoinSemiLattice},
        middle::{
            mir::{self, BasicBlock, Local, Location, VarDebugInfo},
            ty::TyCtxt,
        },
    },
    utils::{Place, PlaceRepacker},
};

use super::domain::{DerefExpansion, MaybeOldPlace};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct DerefExpansions<'tcx>(FxHashSet<DerefExpansion<'tcx>>);

impl<'tcx> DerefExpansions<'tcx> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, location: Location) {
        let mut new: FxHashSet<DerefExpansion<'tcx>> = FxHashSet::default();
        for mut expansion in self.0.clone() {
            let value = if expansion.base.is_current() && place.is_prefix(expansion.base.place()) {
                expansion.make_base_old(location);
                expansion
            } else {
                expansion
            };
            new.insert(value);
        }
        self.0 = new;
    }

    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    pub fn remove(&mut self, expansion: &DerefExpansion<'tcx>) -> bool {
        self.0.remove(expansion)
    }

    pub fn get(
        &self,
        place: MaybeOldPlace<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Vec<MaybeOldPlace<'tcx>>> {
        self.0
            .iter()
            .find(|expansion| expansion.base == place)
            .map(|expansion| expansion.expansion(tcx))
    }

    pub fn get_parents(
        &self,
        place: MaybeOldPlace<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.0
            .iter()
            .filter(|expansion| expansion.expansion(tcx).contains(&place))
            .map(|expansion| expansion.base)
            .collect()
    }

    pub fn ensure_deref_expansion_to_at_least(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        location: Location,
    ) {
        let orig_place = place.place();
        let place_location = place.location();
        let mut in_dag = false;
        for (place, elem) in place.place().iter_projections() {
            let place: Place<'tcx> = place.into();
            if place.is_ref(body, tcx) {
                in_dag = true;
            }
            if in_dag {
                let origin_place = MaybeOldPlace::new(place, place_location);
                if !self.contains_expansion_from(origin_place) {
                    let expansion = match elem {
                        mir::ProjectionElem::Downcast(_, _) | // For downcast we can't blindly expand since we don't know which instance, use this specific one
                        mir::ProjectionElem::Deref // For Box we don't want to expand fields because it's actually an ADT w/ a ptr inside
                        => {
                            vec![place.project_deeper(&[elem], tcx).into()]
                        }
                        _ => place.expand_field(None, PlaceRepacker::new(&body, tcx)),
                    };
                    self.insert(origin_place, expansion, location);
                }
            }
        }
    }

    pub fn ensure_expansion_to_exactly(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        location: Location,
    ) {
        self.ensure_deref_expansion_to_at_least(place, body, tcx, location);
        self.delete_descendants_of(place, tcx, Some(location));
    }

    pub fn move_expansion(
        &mut self,
        old_place: MaybeOldPlace<'tcx>,
        new_place: MaybeOldPlace<'tcx>,
    ) {
        let old_expansion = self.iter().find(|expansion| expansion.base == old_place);
        if let Some(expansion) = old_expansion {
            todo!("Move expansion from {:?} to {:?}", old_place, new_place);
            let mut expansion = expansion.clone();
            self.0.remove(&expansion);
            expansion.base = new_place;
            self.0.insert(expansion);
        } else {
            eprintln!("No expansion found for {:?}", old_place);
        }
    }

    pub fn delete(&mut self, place: MaybeOldPlace<'tcx>) -> bool {
        let mut changed = false;
        for expansion in self
            .iter()
            .filter(|expansion| expansion.base == place)
            .cloned()
            .collect::<Vec<_>>()
        {
            if self.0.remove(&expansion) {
                changed = true
            }
        }
        changed
    }

    pub fn descendants_of(&self, place: MaybeOldPlace<'tcx>) -> Vec<DerefExpansion<'tcx>> {
        self.0
            .iter()
            .filter(|expansion| {
                place.place().is_prefix(expansion.base.place())
                    && place.location() == expansion.base.location()
            })
            .cloned()
            .collect()
    }

    pub fn delete_descendants_of(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        tcx: TyCtxt<'tcx>,
        location: Option<Location>,
    ) -> bool {
        let mut changed = false;
        for expansion in self
            .iter()
            .filter(|expansion| expansion.base == place)
            .cloned()
            .collect::<Vec<_>>()
        {
            for p in expansion.expansion(tcx) {
                if self.delete_descendants_of(p, tcx, location) {
                    changed = true;
                }
                if self.delete(p) {
                    changed = true;
                }
            }
            if self.0.remove(&expansion) {
                changed = true;
            }
        }
        changed
    }

    fn insert(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        expansion: Vec<Place<'tcx>>,
        location: Location,
    ) {
        for p in expansion.iter() {
            assert!(p.projection.len() > place.place().projection.len());
        }
        self.0
            .insert(DerefExpansion::new(place, expansion, location));
    }

    pub fn iter(&self) -> impl Iterator<Item = &DerefExpansion<'tcx>> {
        self.0.iter()
    }

    pub fn contains_expansion_from(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|expansion| expansion.base == place)
    }

    pub fn contains(&self, expansion: &DerefExpansion<'tcx>) -> bool {
        self.0.contains(expansion)
    }

    pub fn has_expansion_at_location(&self, place: Place<'tcx>, location: Location) -> bool {
        self.0
            .iter()
            .any(|expansion| expansion.base.place() == place && expansion.location == location)
    }
}

impl<'tcx> JoinSemiLattice for DerefExpansions<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        // TODO: this is not the correct algorithm
        let mut changed = false;
        for expansion in &other.0 {
            if self.0.insert(expansion.clone()) {
                changed = true;
            }
        }
        changed
    }
}
