use std::rc::Rc;

use serde_json::json;

use crate::{
    rustc_interface::{
        ast::Mutability,
        borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
        data_structures::fx::{FxHashMap, FxHashSet},
        dataflow::{AnalysisDomain, JoinSemiLattice},
        middle::{
            mir::{self, BasicBlock, Local, Location, PlaceElem, VarDebugInfo},
            ty::TyCtxt,
        },
    },
    utils::{Place, PlaceRepacker, PlaceSnapshot},
};

use super::domain::{MaybeOldPlace};
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowDerefExpansion<'tcx> {
    base: MaybeOldPlace<'tcx>,
    expansion: Vec<PlaceElem<'tcx>>,
    location: Location,
}

impl<'tcx> BorrowDerefExpansion<'tcx> {
    pub fn base(&self) -> MaybeOldPlace<'tcx> {
        self.base
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        self.expansion
            .iter()
            .map(|p| self.base.project_deeper(repacker.tcx(), *p))
            .collect()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum DerefExpansion<'tcx> {
    OwnedExpansion {
        base: MaybeOldPlace<'tcx>,
        location: Location,
    },
    BorrowExpansion(BorrowDerefExpansion<'tcx>),
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn location(&self) -> Location {
        match self {
            DerefExpansion::OwnedExpansion { location, .. } => *location,
            DerefExpansion::BorrowExpansion(e) => e.location,
        }
    }

    pub fn borrow_expansion(&self) -> Option<&BorrowDerefExpansion<'tcx>> {
        match self {
            DerefExpansion::BorrowExpansion(e) => Some(e),
            _ => None,
        }
    }

    pub fn borrowed(
        base: MaybeOldPlace<'tcx>,
        expansion: Vec<Place<'tcx>>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        assert!(!base.place().is_owned(repacker.body(), repacker.tcx()));
        assert!(expansion.iter().all(|p| base.place().is_prefix(*p)
            && p.projection.len() == base.place().projection.len() + 1));
        DerefExpansion::BorrowExpansion(BorrowDerefExpansion {
            base,
            expansion: expansion
                .into_iter()
                .map(|p| p.projection.last().unwrap())
                .copied()
                .collect(),
            location,
        })
    }

    pub fn base(&self) -> MaybeOldPlace<'tcx> {
        match self {
            DerefExpansion::OwnedExpansion { base, .. } => *base,
            DerefExpansion::BorrowExpansion(e) => e.base,
        }
    }

    pub fn set_base(&mut self, base: MaybeOldPlace<'tcx>) {
        match self {
            DerefExpansion::OwnedExpansion { base: b, .. } => {
                *b = base;
            }
            DerefExpansion::BorrowExpansion(e) => {
                e.base = base;
            }
        }
    }

    pub fn make_base_old(&mut self, place_location: Location) {
        let base = self.base();
        assert!(base.is_current());
        self.set_base(MaybeOldPlace::OldPlace(PlaceSnapshot {
            place: base.place(),
            at: place_location,
        }));
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base().to_json(repacker),
            "expansion": self.expansion(repacker).iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }

    pub fn expansion_elems(&self) -> Vec<PlaceElem<'tcx>> {
        match self {
            DerefExpansion::OwnedExpansion { .. } => vec![PlaceElem::Deref],
            DerefExpansion::BorrowExpansion(e) => e.expansion.clone(),
        }
    }

    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        match self {
            DerefExpansion::OwnedExpansion { base, .. } => vec![base.project_deref(repacker)],
            DerefExpansion::BorrowExpansion(e) => e.expansion(repacker),
        }
    }
}
