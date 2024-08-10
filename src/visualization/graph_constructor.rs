use crate::{
    borrows::{
        borrows_graph::BorrowsEdgeKind,
        borrows_state::BorrowsState,
        borrows_visitor::{extract_lifetimes, extract_nested_lifetimes, get_vid},
        domain::{AbstractionTarget, AbstractionType, Borrow, MaybeOldPlace, RegionProjection},
        region_abstraction::RegionAbstraction,
        unblock_graph::UnblockGraph,
    },
    combined_pcs::UnblockEdgeType,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
    visualization::dot_graph::RankAnnotation,
};
use serde_derive::Serialize;
use std::{
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
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

use super::{
    dot_graph::DotSubgraph, Graph, GraphEdge, GraphNode, NodeId, NodeType, ReferenceEdgeType,
};

#[derive(Eq, PartialEq, Hash)]
pub struct GraphCluster {
    label: String,
    id: String,
    nodes: BTreeSet<NodeId>,
    min_rank_nodes: Option<BTreeSet<NodeId>>,
}

impl GraphCluster {
    pub fn to_dot_subgraph(&self, nodes: &[GraphNode]) -> DotSubgraph {
        DotSubgraph {
            id: format!("cluster_{}", self.id),
            label: self.label.clone(),
            nodes: self
                .nodes
                .iter()
                .map(|node_id| {
                    nodes
                        .iter()
                        .find(|n| n.id == *node_id)
                        .unwrap()
                        .to_dot_node()
                })
                .collect(),
            rank_annotations: self
                .min_rank_nodes
                .as_ref()
                .map(|nodes| {
                    vec![RankAnnotation {
                        rank_type: "min".to_string(),
                        nodes: nodes.iter().map(|n| n.to_string()).collect(),
                    }]
                })
                .unwrap_or_default(),
        }
    }
}

struct GraphConstructor<'mir, 'tcx> {
    place_nodes: IdLookup<(Place<'tcx>, Option<Location>)>,
    region_projection_nodes: IdLookup<RegionProjection<'tcx>>,
    region_clusters: HashMap<Location, GraphCluster>,
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
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

    fn node_id(&mut self, item: &T) -> NodeId {
        if let Some(idx) = self.existing_id(item) {
            idx
        } else {
            self.1.push(item.clone());
            NodeId(self.0, self.1.len() - 1)
        }
    }
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            place_nodes: IdLookup::new('p'),
            region_projection_nodes: IdLookup::new('r'),
            region_clusters: HashMap::new(),
            nodes: vec![],
            edges: HashSet::new(),
            repacker,
        }
    }

    fn to_graph(self) -> Graph {
        Graph::new(
            self.nodes,
            self.edges,
            self.region_clusters.into_values().collect(),
        )
    }

    fn place_node_id(&mut self, place: Place<'tcx>, location: Option<Location>) -> NodeId {
        self.place_nodes.node_id(&(place, location))
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    fn insert_abstraction_target(&mut self, target: &AbstractionTarget<'tcx>) -> NodeId {
        match target {
            AbstractionTarget::MaybeOldPlace(place) => {
                self.insert_place_node(place.place(), place.location(), None)
            }
            AbstractionTarget::RegionProjection(projection) => {
                self.insert_region_projection_node(projection)
            }
        }
    }

    fn insert_region_projection_node(&mut self, projection: &RegionProjection<'tcx>) -> NodeId {
        if let Some(id) = self.region_projection_nodes.existing_id(projection) {
            return id;
        }
        let id = self.region_projection_nodes.node_id(projection);
        let node = GraphNode {
            id,
            node_type: NodeType::RegionProjectionNode {
                label: format!(
                    "{}↓{:?}",
                    projection.place.to_short_string(self.repacker),
                    projection.region
                ),
            },
        };
        self.insert_node(node);
        id
    }

    fn insert_region_abstraction(&mut self, region_abstraction: &RegionAbstraction<'tcx>) {
        if self
            .region_clusters
            .contains_key(&region_abstraction.location())
        {
            return;
        }

        let mut input_nodes = BTreeSet::new();
        let mut output_nodes = BTreeSet::new();

        for edge in region_abstraction.edges() {
            let input = self.insert_abstraction_target(&edge.input);
            let output = self.insert_abstraction_target(&edge.output);
            input_nodes.insert(input);
            output_nodes.insert(output);
            self.edges.insert(GraphEdge::AbstractEdge {
                blocked: input,
                blocking: output,
            });
        }

        assert!(!input_nodes.is_empty());
        let cluster = GraphCluster {
            id: format!(
                "c{:?}_{}",
                region_abstraction.location().block,
                region_abstraction.location().statement_index
            ),
            label: format!("{:?}", region_abstraction.location()),
            nodes: input_nodes
                .iter()
                .chain(output_nodes.iter())
                .cloned()
                .collect(),
            min_rank_nodes: Some(input_nodes),
        };
        self.region_clusters
            .insert(region_abstraction.location(), cluster);
    }

    fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<Location>,
        capability: Option<CapabilityKind>,
    ) -> NodeId {
        if let Some(node_id) = self.place_nodes.existing_id(&(place, location)) {
            return node_id;
        }
        let id = self.place_node_id(place, location);
        let label = format!("{:?}", place.to_string(self.repacker));
        let region = match place.ty(self.repacker).ty.kind() {
            ty::TyKind::Ref(region, _, _) => Some(format!("{:?}", region)),
            _ => None,
        };
        let node_type = if place.is_owned(self.repacker.body(), self.repacker.tcx()) {
            NodeType::FPCSNode {
                label,
                capability,
                location,
                region,
            }
        } else {
            assert!(capability.is_none());
            NodeType::ReborrowingDagNode { label, location }
        };
        if place.is_owned(self.repacker.body(), self.repacker.tcx()) {
            for lifetime in extract_nested_lifetimes(place.ty(self.repacker).ty) {
                let region_projection = RegionProjection {
                    place: MaybeOldPlace::Current {
                        place: place.clone(),
                    },
                    region: get_vid(&lifetime).unwrap(),
                };
                self.insert_region_projection_node(&region_projection);
            }
        }
        let node = GraphNode { id, node_type };
        self.insert_node(node);
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
                            reason: "".to_string(),
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
                                reason: "".to_string(),
                            });
                    }
                }
                UnblockEdgeType::Abstraction(region_edge) => {
                    for place in region_edge.blocked_places() {
                        let blocked_node = self.constructor.insert_place_node(
                            place.place(),
                            place.location(),
                            None,
                        );
                        for place in &region_edge.blocker_places() {
                            let blocking_node = self.constructor.insert_place_node(
                                place.place(),
                                place.location(),
                                None,
                            );
                            self.constructor.edges.insert(GraphEdge::AbstractEdge {
                                blocked: blocked_node,
                                blocking: blocking_node,
                            });
                        }
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
    repacker: PlaceRepacker<'a, 'tcx>,
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
            repacker,
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

        for edge in self.borrows_domain.graph_edges() {
            match edge.kind() {
                BorrowsEdgeKind::DerefExpansion(deref_expansion) => {
                    let base = self.insert_maybe_old_place(deref_expansion.base());
                    for place in deref_expansion.expansion(self.repacker) {
                        let place = self.insert_maybe_old_place(place);
                        self.constructor
                            .edges
                            .insert(GraphEdge::DerefExpansionEdge {
                                source: base,
                                target: place,
                                location: deref_expansion.location(),
                            });
                    }
                }
                BorrowsEdgeKind::Reborrow(reborrow) => {
                    let borrowed_place = self.insert_maybe_old_place(reborrow.blocked_place);
                    let assigned_place = self.insert_maybe_old_place(reborrow.assigned_place);
                    self.constructor.edges.insert(GraphEdge::ReborrowEdge {
                        borrowed_place,
                        assigned_place,
                        location: reborrow.location,
                        region: format!("{:?}", reborrow.region),
                        path_conditions: format!("{:?}", reborrow.location.block),
                    });
                }
                _ => {}
            }
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

        for abstraction in self.borrows_domain.region_abstractions().iter() {
            let r = self.constructor.insert_region_abstraction(abstraction);
        }

        for member in self.borrows_domain.region_projection_members().iter() {
            let place = self.insert_maybe_old_place(member.place);
            let region_projection = self
                .constructor
                .insert_region_projection_node(&member.projection);
            self.constructor
                .edges
                .insert(GraphEdge::RegionProjectionMemberEdge {
                    place,
                    region_projection,
                });
        }

        self.constructor.to_graph()
    }
}
