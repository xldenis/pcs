use std::rc::Rc;

use crate::{
    rustc_interface::{
        ast::Mutability,
        borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
        data_structures::fx::{FxHashMap, FxHashSet},
        dataflow::{AnalysisDomain, JoinSemiLattice},
        middle::{
            mir::{self, BasicBlock, Location, VarDebugInfo},
            ty::TyCtxt,
        },
    },
    utils::{Place, PlaceRepacker},
};

use super::domain::{DerefExpansion, MaybeOldPlace};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct DerefExpansions<'tcx>(FxHashSet<DerefExpansion<'tcx>>);

impl<'tcx> DerefExpansions<'tcx> {
    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    pub fn get(&self, place: MaybeOldPlace<'tcx>) -> Option<Vec<Place<'tcx>>> {
        self.0
            .iter()
            .find(|expansion| expansion.base == place)
            .map(|expansion| expansion.expansion.clone())
    }

    pub fn get_parent(&self, place: MaybeOldPlace<'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        self.0
            .iter()
            .find(|expansion| {
                expansion.base.location() == place.location()
                    && expansion.expansion.contains(&place.place())
            })
            .map(|expansion| expansion.base)
    }

    pub fn ensure_expansion_to(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        block: BasicBlock,
    ) {
        let orig_place = place.place();
        let location = place.location();
        let mut in_dag = false;
        for (place, elem) in place.place().iter_projections() {
            let place: Place<'tcx> = place.into();
            if place.is_ref(body, tcx) {
                in_dag = true;
            }
            if in_dag {
                let origin_place = MaybeOldPlace::new(place, location);
                if !self.contains_projection_from(origin_place) {
                    let expansion = match elem {
                        mir::ProjectionElem::Downcast(_, _) | // For downcast we can't blindly expand since we don't know which instance, use this specific one
                        mir::ProjectionElem::Deref // For Box we don't want to expand fields because it's actually an ADT w/ a ptr inside
                        => {
                            vec![place.project_deeper(&[elem], tcx).into()]
                        }
                        _ => place.expand_field(None, PlaceRepacker::new(&body, tcx)),
                    };
                    // eprintln!("Expand to {:?} for {:?}", expansion, orig_place);
                    self.insert(origin_place, expansion, block);
                }
            }
        }
        self.delete_descendants_of(place);
    }

    fn delete(&mut self, place: MaybeOldPlace<'tcx>) -> bool {
        let mut changed = false;
        for expansion in self
            .iter()
            .filter(|expansion| expansion.base == place)
            .cloned()
            .collect::<Vec<_>>()
        {
            if self.0.remove(&expansion) {
                eprintln!("Deleted expansion: {:?}", expansion);
                changed = true
            }
        }
        changed
    }

    pub fn delete_descendants_of(&mut self, place: MaybeOldPlace<'tcx>) -> bool {
        let mut changed = false;
        for expansion in self
            .iter()
            .filter(|expansion| expansion.base == place)
            .cloned()
            .collect::<Vec<_>>()
        {
            for e in expansion.expansion.iter() {
                let p = MaybeOldPlace::new(*e, None);
                if self.delete_descendants_of(p) {
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
        block: BasicBlock,
    ) {
        for p in expansion.iter() {
            assert!(p.projection.len() > place.place().projection.len());
        }
        self.0.insert(DerefExpansion::new(place, expansion, block));
    }

    pub fn iter(&self) -> impl Iterator<Item = &DerefExpansion<'tcx>> {
        self.0.iter()
    }

    pub fn contains_projection_from(&self, place: MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|expansion| expansion.base == place)
    }

    pub fn contains(&self, expansion: &DerefExpansion<'tcx>) -> bool {
        self.0.contains(expansion)
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
