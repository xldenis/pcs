use crate::{
    borrows::{
        borrows_state::BorrowsState,
        domain::{AbstractionType, Borrow, MaybeOldPlace},
        unblock_graph::UnblockGraph,
    },
    combined_pcs::UnblockEdgeType,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
};
use serde_derive::Serialize;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::File,
    io::{self, Write},
    ops::Deref,
    rc::Rc,
};

use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            calculate_borrows_out_of_scope_at_location, BorrowIndex, Borrows, LocationTable,
            PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
    },
    data_structures::fx::{FxHashMap, FxIndexMap},
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    middle::{
        mir::{
            self, BinOp, Body, Local, Location, Operand, PlaceElem, Promoted, Rvalue, Statement,
            TerminatorKind, UnwindAction, VarDebugInfo, RETURN_PLACE,
        },
        ty::{self, GenericArgsRef, ParamEnv, RegionVid, TyCtxt},
    },
};

use super::{Graph, GraphEdge, GraphNode, NodeId, NodeType, ReferenceEdgeType};

struct GraphConstructor<'mir, 'tcx> {
    place_nodes: IdLookup<(Place<'tcx>, Option<Location>)>,
    region_abstraction_nodes: IdLookup<RegionVid>,
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
    rank: HashMap<NodeId, usize>,
    repacker: PlaceRepacker<'mir, 'tcx>,
}

struct IdLookup<T>(char, Vec<T>);

impl<T: Eq + Clone> IdLookup<T> {
    fn new(prefix: char) -> Self {
        Self(prefix, vec![])
    }

    fn existing_id(&mut self, item: &T) -> Option<NodeId> {
        self.1
            .iter()
            .position(|x| x == item)
            .map(|idx| NodeId(self.0, idx))
    }

    fn node_id(&mut self, item: T) -> NodeId {
        if let Some(idx) = self.existing_id(&item) {
            idx
        } else {
            self.1.push(item);
            NodeId(self.0, self.1.len() - 1)
        }
    }
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            place_nodes: IdLookup::new('p'),
            region_abstraction_nodes: IdLookup::new('r'),
            nodes: vec![],
            edges: HashSet::new(),
            rank: HashMap::new(),
            repacker,
        }
    }

    fn to_graph(self) -> Graph {
        let mut nodes = self.nodes.clone().into_iter().collect::<Vec<_>>();
        nodes.sort_by(|a, b| self.rank(a.id).cmp(&self.rank(b.id)));
        Graph::new(nodes, self.edges)
    }

    fn place_node_id(&mut self, place: Place<'tcx>, location: Option<Location>) -> NodeId {
        self.place_nodes.node_id((place, location))
    }

    fn rank(&self, node: NodeId) -> usize {
        *self.rank.get(&node).unwrap_or(&usize::MAX)
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    fn insert_region_abstraction_node(
        &mut self,
        region: RegionVid,
        abstraction_type: &AbstractionType,
    ) -> NodeId {
        if let Some(id) = self.region_abstraction_nodes.existing_id(&region) {
            return id;
        }
        let call_location = match abstraction_type {
            AbstractionType::FunctionCall { location, .. } => location,
        };
        let id = self.region_abstraction_nodes.node_id(region);
        let label = format!("{:?} for call at {:?}", region, call_location);
        let node = GraphNode {
            id,
            node_type: NodeType::RegionAbstractionNode { label },
        };
        self.insert_node(node);
        id
    }

    fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<Location>,
        kind: Option<CapabilityKind>,
    ) -> NodeId {
        if let Some(node_id) = self.place_nodes.existing_id(&(place, location)) {
            return node_id;
        }
        let id = self.place_node_id(place, location);
        let label = format!("{:?}", place.to_string(self.repacker));
        let node = GraphNode {
            id,
            node_type: NodeType::PlaceNode {
                label,
                capability: kind,
                location,
            },
        };
        self.insert_node(node);
        self.rank.insert(id, place.local.as_usize());
        id
    }
}

pub struct UnblockGraphConstructor<'a, 'tcx> {
    unblock_graph: UnblockGraph<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
}

impl<'a, 'tcx> UnblockGraphConstructor<'a, 'tcx> {
    pub fn new(unblock_graph: UnblockGraph<'tcx>, repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            unblock_graph,
            constructor: GraphConstructor::new(repacker),
        }
    }

    pub fn construct_graph(mut self) -> Graph {
        for edge in self.unblock_graph.edges() {
            match &edge.edge_type {
                UnblockEdgeType::Reborrow {
                    is_mut,
                    blocker,
                    blocked,
                } => {
                    let blocked_place = self.constructor.insert_place_node(
                        blocked.place(),
                        blocked.location(),
                        None,
                    );
                    let blocking_place = self.constructor.insert_place_node(
                        blocker.place(),
                        blocker.location(),
                        None,
                    );
                    self.constructor
                        .edges
                        .insert(GraphEdge::UnblockReborrowEdge {
                            blocked_place,
                            blocking_place,
                            block: edge.block,
                            reason: format!("{:?}", edge.reason),
                        });
                }
                UnblockEdgeType::Projection(proj_edge) => {
                    let blocked_place = self.constructor.insert_place_node(
                        proj_edge.blocked.place(),
                        proj_edge.blocked.location(),
                        None,
                    );
                    for blocker in proj_edge.blocker_places(self.constructor.repacker.tcx()) {
                        let blocking_place = self.constructor.insert_place_node(
                            blocker.place(),
                            blocker.location(),
                            None,
                        );
                        self.constructor
                            .edges
                            .insert(GraphEdge::UnblockProjectionEdge {
                                blocked_place,
                                blocking_place,
                                block: edge.block,
                                reason: format!("{:?}", edge.reason),
                            });
                    }
                }
                UnblockEdgeType::Region(region_edge) => {
                    let region = self.constructor.insert_region_abstraction_node(
                        region_edge.region_vid(),
                        region_edge.abstraction_type(),
                    );
                    for place in region_edge.blocked_places() {
                        let place = self.constructor.insert_place_node(
                            place.place(),
                            place.location(),
                            None,
                        );
                        self.constructor
                            .edges
                            .insert(GraphEdge::RegionBlocksPlaceEdge { region, place });
                    }
                    for place in &region_edge.blocker_places {
                        let place = self.constructor.insert_place_node(
                            place.place(),
                            place.location(),
                            None,
                        );
                        self.constructor
                            .edges
                            .insert(GraphEdge::RegionBlockedByPlaceEdge { region, place });
                    }
                }
            }
        }
        self.constructor.to_graph()
    }
}

pub struct PCSGraphConstructor<'a, 'tcx> {
    summary: &'a CapabilitySummary<'tcx>,
    borrows_domain: &'a BorrowsState<'a, 'tcx>,
    borrow_set: &'a BorrowSet<'tcx>,
    constructor: GraphConstructor<'a, 'tcx>,
}

impl<'a, 'tcx> PCSGraphConstructor<'a, 'tcx> {
    pub fn new(
        summary: &'a CapabilitySummary<'tcx>,
        repacker: PlaceRepacker<'a, 'tcx>,
        borrows_domain: &'a BorrowsState<'a, 'tcx>,
        borrow_set: &'a BorrowSet<'tcx>,
    ) -> Self {
        Self {
            summary,
            borrows_domain,
            borrow_set,
            constructor: GraphConstructor::new(repacker),
        }
    }

    fn insert_place_and_previous_projections(
        &mut self,
        place: Place<'tcx>,
        location: Option<Location>,
        kind: Option<CapabilityKind>,
    ) -> NodeId {
        let node = self.constructor.insert_place_node(place, location, kind);
        if location.is_some() {
            return node;
        }
        let mut projection = place.projection;
        let mut last_node = node;
        while !projection.is_empty() {
            projection = &projection[..projection.len() - 1];
            let place = Place::new(place.local, &projection);
            let node = self.constructor.insert_place_node(place, None, None);
            self.constructor.edges.insert(GraphEdge::ProjectionEdge {
                source: node,
                target: last_node,
            });
            last_node = node.clone();
        }
        node
    }

    fn insert_maybe_old_place(&mut self, place: MaybeOldPlace<'tcx>) -> NodeId {
        match place {
            MaybeOldPlace::Current { place } => {
                self.constructor
                    .insert_place_node(place, None, self.capability_for_place(place))
            }
            MaybeOldPlace::OldPlace(snapshot_place) => self.insert_snapshot_place(snapshot_place),
        }
    }

    fn insert_place(&mut self, place: Place<'tcx>) -> NodeId {
        self.constructor
            .insert_place_node(place, None, self.capability_for_place(place))
    }

    fn insert_snapshot_place(&mut self, place: PlaceSnapshot<'tcx>) -> NodeId {
        let cap = self.capability_for_place(place.place);
        self.insert_place_and_previous_projections(place.place, Some(place.at), cap)
    }

    fn capability_for_place(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        match self.summary.get(place.local) {
            Some(CapabilityLocal::Allocated(projections)) => {
                projections.deref().get(&place).cloned()
            }
            _ => None,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.constructor.repacker.tcx()
    }

    pub fn construct_graph(mut self) -> Graph {
        for (local, capability) in self.summary.iter().enumerate() {
            match capability {
                CapabilityLocal::Unallocated => {}
                CapabilityLocal::Allocated(projections) => {
                    for (place, kind) in projections.iter() {
                        self.insert_place_and_previous_projections(*place, None, Some(*kind));
                    }
                }
            }
        }
        for deref_expansion in self.borrows_domain.deref_expansions.iter() {
            let base = self.insert_maybe_old_place(deref_expansion.base);
            for place in deref_expansion.expansion(self.tcx()) {
                let place = self.insert_maybe_old_place(place);
                self.constructor
                    .edges
                    .insert(GraphEdge::DerefExpansionEdge {
                        source: base,
                        target: place,
                        location: deref_expansion.location,
                    });
            }
        }

        for reborrow in self.borrows_domain.reborrows().iter() {
            let borrowed_place = self.insert_maybe_old_place(reborrow.blocked_place);
            let assigned_place = self.insert_maybe_old_place(reborrow.assigned_place);
            self.constructor.edges.insert(GraphEdge::ReborrowEdge {
                borrowed_place,
                assigned_place,
                location: reborrow.location,
            });
        }

        let mut before_places: HashSet<(Place<'tcx>, Location)> = HashSet::new();
        for (place, location) in before_places.iter() {
            for (place2, location2) in before_places.iter() {
                if location == location2 && place2.is_deref_of(*place) {
                    let source = self.constructor.place_node_id(*place, Some(*location));
                    let target = self.constructor.place_node_id(*place2, Some(*location));
                    self.constructor
                        .edges
                        .insert(GraphEdge::ProjectionEdge { source, target });
                }
            }
        }

        for abstraction in self.borrows_domain.region_abstractions.iter() {
            let r = self
                .constructor
                .insert_region_abstraction_node(abstraction.region, &abstraction.abstraction_type);
            for vid in &abstraction.blocks_abstractions {
                let blocked = self
                    .constructor
                    .insert_region_abstraction_node(*vid, &abstraction.abstraction_type);
                self.constructor
                    .edges
                    .insert(GraphEdge::BlocksAbstractionEdge {
                        blocked_region: blocked,
                        blocking_region: r,
                    });
            }
            for place in &abstraction.blocked_by_places() {
                let place = self.insert_maybe_old_place(*place);
                self.constructor
                    .edges
                    .insert(GraphEdge::RegionBlockedByPlaceEdge { region: r, place });
            }
            for place in &abstraction.blocks_places() {
                let place = self.insert_maybe_old_place(*place);
                self.constructor
                    .edges
                    .insert(GraphEdge::RegionBlocksPlaceEdge { region: r, place });
            }
        }

        self.constructor.to_graph()
    }
}
