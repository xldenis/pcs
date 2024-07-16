use crate::{
    borrows::domain::{Borrow, BorrowsState, MaybeOldPlace, PlaceSnapshot, RegionAbstraction},
    combined_pcs::{UnblockEdgeType, UnblockGraph},
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker},
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
    inserted_nodes: Vec<(Place<'tcx>, Option<Location>)>,
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
    rank: HashMap<NodeId, usize>,
    repacker: PlaceRepacker<'mir, 'tcx>,
}

impl<'a, 'tcx> GraphConstructor<'a, 'tcx> {
    fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        Self {
            inserted_nodes: vec![],
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

    fn existing_node_id(&self, place: Place<'tcx>, location: Option<Location>) -> Option<NodeId> {
        self.inserted_nodes
            .iter()
            .position(|(p, n)| *p == place && *n == location)
            .map(|idx| NodeId(idx))
    }

    fn node_id(&mut self, place: Place<'tcx>, location: Option<Location>) -> NodeId {
        if let Some(idx) = self.existing_node_id(place, location) {
            idx
        } else {
            self.inserted_nodes.push((place, location));
            NodeId(self.inserted_nodes.len() - 1)
        }
    }

    fn rank(&self, node: NodeId) -> usize {
        *self.rank.get(&node).unwrap_or(&usize::MAX)
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<Location>,
        kind: Option<CapabilityKind>,
    ) -> NodeId {
        if let Some(node_id) = self.existing_node_id(place, location) {
            return node_id;
        }
        let id = self.node_id(place, location);
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
            let source = self.constructor.insert_place_node(
                edge.blocked.place(),
                edge.blocked.location(),
                None,
            );
            let target = self.constructor.insert_place_node(
                edge.blocker.place(),
                edge.blocker.location(),
                None,
            );
            match edge.edge_type {
                UnblockEdgeType::Reborrow { is_mut } => {
                    self.constructor
                        .edges
                        .insert(GraphEdge::UnblockReborrowEdge {
                            blocked_place: source,
                            blocking_place: target,
                            block: edge.block,
                            reason: edge.reason.clone(),
                        });
                }
                UnblockEdgeType::Projection(_) => {
                    self.constructor
                        .edges
                        .insert(GraphEdge::UnblockProjectionEdge {
                            blocked_place: source,
                            blocking_place: target,
                            block: edge.block,
                            reason: edge.reason.clone(),
                        });
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
            for expansion in deref_expansion.expansion.iter() {
                let place = match deref_expansion.base {
                    MaybeOldPlace::Current { place } => {
                        MaybeOldPlace::Current { place: *expansion }
                    }
                    MaybeOldPlace::OldPlace(snapshot_place) => {
                        MaybeOldPlace::OldPlace(PlaceSnapshot {
                            place: *expansion,
                            at: snapshot_place.at,
                        })
                    }
                };
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
        // for borrow in self.borrows_domain.borrows().iter() {
        //     let borrowed_place = self.insert_place(borrow.borrowed_place);
        //     let assigned_place = self.insert_place(borrow.assigned_place);
        //     let borrow_data = &self.borrow_set[borrow.index];
        //     self.constructor.edges.insert(GraphEdge::ReferenceEdge {
        //         borrowed_place,
        //         assigned_place,
        //         edge_type: ReferenceEdgeType::RustcBorrow(borrow.index, borrow_data.region),
        //     });
        // }
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
                    let source = self.constructor.node_id(*place, Some(*location));
                    let target = self.constructor.node_id(*place2, Some(*location));
                    self.constructor
                        .edges
                        .insert(GraphEdge::ProjectionEdge { source, target });
                }
            }
        }

        self.constructor.to_graph()
    }
}
