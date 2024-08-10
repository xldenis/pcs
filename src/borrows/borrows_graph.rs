use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Local, Location, PlaceElem, VarDebugInfo},
    middle::ty::{self, Region, RegionVid, TyCtxt},
};
use serde_json::{json, Value};

use crate::{
    combined_pcs::PlaceCapabilitySummary,
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary,
        FreePlaceCapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::{
    borrows_state::{
        RegionProjectionMember, RegionProjectionMemberDirection, RegionProjectionMembers,
    },
    borrows_visitor::DebugCtx,
    deref_expansion::DerefExpansion,
    domain::{Borrow, Latest, MaybeOldPlace, Reborrow, RegionProjection},
    path_condition::{PathCondition, PathConditions},
    region_abstraction::{RegionAbstraction, RegionAbstractions},
    unblock_graph::UnblockGraph,
};
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BorrowsGraph<'tcx>(FxHashSet<BorrowsEdge<'tcx>>);

impl<'tcx> BorrowsGraph<'tcx> {
    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    pub fn edges(&self) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.0.iter()
    }

    pub fn kill_reborrows(
        &mut self,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: MaybeOldPlace<'tcx>,
    ) -> bool {
        self.0.retain(|edge| {
            if let BorrowsEdgeKind::Reborrow(reborrow) = &edge.kind {
                reborrow.blocked_place != blocked_place || reborrow.assigned_place != assigned_place
            } else {
                true
            }
        });
        true
    }

    pub fn region_abstractions(&self) -> FxHashSet<RegionAbstraction<'tcx>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind {
                BorrowsEdgeKind::RegionAbstraction(abstraction) => Some(abstraction),
                _ => None,
            })
            .cloned()
            .collect()
    }

    // TODO: Delete?
    pub fn deref_expansions(&self) -> FxHashSet<DerefExpansion<'tcx>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind {
                BorrowsEdgeKind::DerefExpansion(de) => Some(de),
                _ => None,
            })
            .cloned()
            .collect()
    }

    // TODO: Delete?
    pub fn reborrows(&self) -> FxHashSet<Reborrow<'tcx>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind {
                BorrowsEdgeKind::Reborrow(reborrow) => Some(reborrow),
                _ => None,
            })
            .cloned()
            .collect()
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.0.iter().any(|edge| match &edge.kind {
            BorrowsEdgeKind::Reborrow(reborrow) => reborrow.location == location,
            _ => false,
        })
    }

    pub fn reborrows_blocked_by(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<Reborrow<'tcx>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind {
                BorrowsEdgeKind::Reborrow(reborrow) => {
                    if reborrow.assigned_place == place {
                        Some(reborrow)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .cloned()
            .collect()
    }

    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<Place<'tcx>> {
        let mut candidates = self
            .0
            .iter()
            .flat_map(|edge| {
                edge.blocked_places()
                    .into_iter()
                    .flat_map(|p| p.as_current())
            })
            .collect::<FxHashSet<_>>();
        candidates.retain(|p| !self.has_edge_to((*p).into(), repacker));
        candidates
    }

    pub fn has_edge_to(
        &self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.0
            .iter()
            .any(|edge| edge.target_places(repacker).contains(&place))
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) {
        self.mut_edges(|edge| {
            edge.make_place_old(place, latest);
            true
        });
    }

    // TODO: Join paths
    pub fn join(&mut self, other: &Self) -> bool {
        let len = self.0.len();
        self.0.extend(other.0.iter().cloned());
        self.0.len() != len
    }

    // TODO: Delete?
    pub fn region_projection_members(&self) -> RegionProjectionMembers<'tcx> {
        RegionProjectionMembers(
            self.0
                .iter()
                .filter_map(|edge| match &edge.kind {
                    BorrowsEdgeKind::RegionProjectionMember(member) => Some(member),
                    _ => None,
                })
                .cloned()
                .collect(),
        )
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: Region<'tcx>,
    ) -> bool {
        self.insert(
            Reborrow {
                region,
                mutability,
                blocked_place: MaybeOldPlace::Current {
                    place: blocked_place,
                },
                assigned_place: MaybeOldPlace::Current {
                    place: assigned_place,
                },
                location,
            }
            .to_borrows_edge(PathConditions::new(location.block)),
        )
    }

    pub fn insert(&mut self, edge: BorrowsEdge<'tcx>) -> bool {
        self.0.insert(edge)
    }

    pub fn ensure_expansion_to_exactly(
        &mut self,
        place: Place<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        location: Location,
    ) {
        eprintln!("{:?} ensure_expansion_to_exactly {:?}", location, place);
        self.ensure_deref_expansion_to_at_least(place, body, tcx, location);
        self.delete_descendants_of(
            place.into(),
            PlaceRepacker::new(body, tcx),
            DebugCtx::new(location),
        );
    }

    pub fn edges_blocking(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.0
            .iter()
            .filter(move |edge| edge.blocked_places().contains(&place))
    }

    pub fn remove_abstraction_at(&mut self, location: Location) {
        self.0.retain(|edge| {
            if let BorrowsEdgeKind::RegionAbstraction(abstraction) = &edge.kind {
                abstraction.location() != location
            } else {
                true
            }
        });
    }

    pub fn delete_descendants_of(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: DebugCtx,
    ) -> bool {
        let mut changed = false;
        let edges = self.edges_blocking(place).cloned().collect::<Vec<_>>();
        for edge in edges {
            changed = true;
            self.remove(&edge, debug_ctx);
        }
        changed
    }

    pub fn remove(&mut self, edge: &BorrowsEdge<'tcx>, debug_ctx: DebugCtx) -> bool {
        match debug_ctx.location() {
            Some(location) if location.statement_index == 5 => {
                eprintln!("Stack trace:");
                let backtrace = std::backtrace::Backtrace::capture();
                eprintln!("{}", backtrace);
                eprintln!("{:?} remove {:?}", location, edge)
            }
            _ => {}
        }
        self.0.remove(edge)
    }

    pub fn move_region_projection_member_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.mut_edges(|edge| {
            if let BorrowsEdgeKind::RegionProjectionMember(member) = &mut edge.kind {
                if member.projection.place == old_projection_place {
                    let idx = member.projection_index(repacker);
                    member.projection = new_projection_place.region_projection(idx, repacker);
                }
            }
            true
        });
    }

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        self.mut_edges(|edge| {
            if let BorrowsEdgeKind::Reborrow(reborrow) = &mut edge.kind {
                if reborrow.assigned_place == orig_assigned_place {
                    reborrow.assigned_place = new_assigned_place;
                }
            }
            true
        });
    }

    pub fn contains_deref_expansion_from(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|edge| {
            if let BorrowsEdgeKind::DerefExpansion(de) = &edge.kind {
                de.base() == *place
            } else {
                false
            }
        })
    }

    pub fn ensure_deref_expansion_to_at_least(
        &mut self,
        place: Place<'tcx>,
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        location: Location,
    ) {
        let mut in_dag = false;
        for (place, elem) in place.iter_projections() {
            let place: Place<'tcx> = place.into();
            if place.is_ref(body, tcx) {
                in_dag = true;
            }
            if in_dag {
                let origin_place = place.into();
                if !self.contains_deref_expansion_from(&origin_place) {
                    let expansion = match elem {
                        mir::ProjectionElem::Downcast(_, _) | // For downcast we can't blindly expand since we don't know which instance, use this specific one
                        mir::ProjectionElem::Deref // For Box we don't want to expand fields because it's actually an ADT w/ a ptr inside
                        => {
                            vec![place.project_deeper(&[elem], tcx).into()]
                        }
                        _ => place.expand_field(None, PlaceRepacker::new(&body, tcx)),
                    };
                    self.insert_deref_expansion(
                        origin_place,
                        expansion,
                        location,
                        PlaceRepacker::new(&body, tcx),
                    );
                }
            }
        }
    }

    fn insert_deref_expansion(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        expansion: Vec<Place<'tcx>>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for p in expansion.iter() {
            assert!(p.projection.len() > place.place().projection.len());
        }
        let de = if place.place().is_owned(repacker.body(), repacker.tcx()) {
            DerefExpansion::OwnedExpansion {
                base: place,
                location,
            }
        } else {
            DerefExpansion::borrowed(place, expansion, location, repacker)
        };
        self.insert(BorrowsEdge {
            conditions: PathConditions::new(location.block),
            kind: BorrowsEdgeKind::DerefExpansion(de),
        });
    }

    fn mut_edges(&mut self, mut f: impl FnMut(&mut BorrowsEdge<'tcx>) -> bool) -> bool {
        let mut changed = false;
        self.0 = self
            .0
            .drain()
            .map(|mut edge| {
                if f(&mut edge) {
                    changed = true;
                }
                edge
            })
            .collect();
        changed
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.0.retain(|edge| edge.conditions.valid_for_path(path));
    }

    pub fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.mut_edges(|edge| edge.conditions.insert(pc.clone()))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowsEdge<'tcx> {
    conditions: PathConditions,
    kind: BorrowsEdgeKind<'tcx>,
}

impl<'tcx> BorrowsEdge<'tcx> {
    pub fn kind(&self) -> &BorrowsEdgeKind<'tcx> {
        &self.kind
    }

    pub fn new(kind: BorrowsEdgeKind<'tcx>, block: BasicBlock) -> Self {
        Self {
            conditions: PathConditions::new(block),
            kind,
        }
    }
    pub fn blocked_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.kind.blocked_places()
    }

    pub fn target_places(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.kind.target_places(repacker)
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.kind.make_place_old(place, latest);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowsEdgeKind<'tcx> {
    Reborrow(Reborrow<'tcx>),
    DerefExpansion(DerefExpansion<'tcx>),
    RegionAbstraction(RegionAbstraction<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>),
}

impl<'tcx> BorrowsEdgeKind<'tcx> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        match self {
            BorrowsEdgeKind::Reborrow(reborrow) => reborrow.make_place_old(place, latest),
            BorrowsEdgeKind::DerefExpansion(de) => de.make_place_old(place, latest),
            BorrowsEdgeKind::RegionAbstraction(abstraction) => {
                abstraction.make_place_old(place, latest)
            }
            BorrowsEdgeKind::RegionProjectionMember(member) => member.make_place_old(place, latest),
        }
    }

    pub fn blocked_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match &self {
            BorrowsEdgeKind::Reborrow(reborrow) => {
                vec![reborrow.blocked_place].into_iter().collect()
            }
            BorrowsEdgeKind::DerefExpansion(de) => vec![de.base()].into_iter().collect(),
            BorrowsEdgeKind::RegionAbstraction(ra) => ra.blocks_places(),
            BorrowsEdgeKind::RegionProjectionMember(member) => match member.direction {
                RegionProjectionMemberDirection::PlaceIsRegionInput => {
                    vec![member.place].into_iter().collect()
                }
                RegionProjectionMemberDirection::PlaceIsRegionOutput => FxHashSet::default(),
            },
        }
    }

    pub fn target_places(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        match &self {
            BorrowsEdgeKind::Reborrow(reborrow) => {
                vec![reborrow.assigned_place].into_iter().collect()
            }
            BorrowsEdgeKind::DerefExpansion(de) => de.expansion(repacker).into_iter().collect(),
            BorrowsEdgeKind::RegionAbstraction(ra) => ra.blocked_by_places(),
            BorrowsEdgeKind::RegionProjectionMember(member) => match member.direction {
                RegionProjectionMemberDirection::PlaceIsRegionInput => FxHashSet::default(),
                RegionProjectionMemberDirection::PlaceIsRegionOutput => {
                    vec![member.place].into_iter().collect()
                }
            },
        }
    }
}

pub trait ToBorrowsEdge<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for DerefExpansion<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::DerefExpansion(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for RegionAbstraction<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::RegionAbstraction(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for Reborrow<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::Reborrow(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for RegionProjectionMember<'tcx> {
    fn to_borrows_edge(self, conditions: PathConditions) -> BorrowsEdge<'tcx> {
        BorrowsEdge {
            conditions,
            kind: BorrowsEdgeKind::RegionProjectionMember(self),
        }
    }
}

pub struct Conditioned<T> {
    pub conditions: PathConditions,
    pub value: T,
}

impl<'tcx, T: ToBorrowsEdge<'tcx>> Conditioned<T> {
    pub fn to_borrows_edge(self) -> BorrowsEdge<'tcx> {
        self.value.to_borrows_edge(self.conditions)
    }
}
