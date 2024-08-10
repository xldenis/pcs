// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod dot_graph;
pub mod drawer;
pub mod graph_constructor;
pub mod mir_graph;

use crate::{
    borrows::{
        borrows_state::BorrowsState,
        unblock_graph::UnblockGraph,
    },
    free_pcs::{CapabilityKind, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker},
};
use std::{
    collections::{HashSet},
    fs::File,
    io::{self, Write},
};

use dot::escape_html;
use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex,
            PoloniusInput,
        },
    },
    middle::{
        mir::{
            BasicBlock, Location,
        },
        ty::{RegionVid},
    },
};

use self::{
    dot_graph::{
        DotEdge, DotFloatAttr, DotLabel, DotNode, DotStringAttr, EdgeDirection, EdgeOptions,
    },
    graph_constructor::{GraphCluster, PCSGraphConstructor, UnblockGraphConstructor},
};

pub fn place_id<'tcx>(place: &Place<'tcx>) -> String {
    format!("{:?}", place)
}

struct GraphDrawer<T: io::Write> {
    out: T,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
struct NodeId(char, usize);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct GraphNode {
    id: NodeId,
    node_type: NodeType,
}

impl GraphNode {
    fn to_dot_node(&self) -> DotNode {
        match &self.node_type {
            NodeType::ReborrowingDagNode { label, location } => {
                let location_text = match location {
                    Some(l) => escape_html(&format!(" at {:?}", l)),
                    None => "".to_string(),
                };
                let label = format!(
                    "<FONT FACE=\"courier\">{}</FONT>&nbsp;{}",
                    escape_html(&label),
                    escape_html(&location_text)
                );
                DotNode {
                    id: self.id.to_string(),
                    label: DotLabel::Html(label.clone()),
                    color: DotStringAttr("darkgreen".to_string()),
                    font_color: DotStringAttr("darkgreen".to_string()),
                    shape: DotStringAttr("rect".to_string()),
                    style: Some(DotStringAttr("rounded".to_string())),
                    penwidth: Some(DotFloatAttr(1.5)),
                }
            }
            NodeType::FPCSNode {
                capability,
                location,
                label,
                region,
            } => {
                let capability_text = match capability {
                    Some(k) => format!("{:?}", k),
                    None => "".to_string(),
                };
                let location_text = match location {
                    Some(l) => escape_html(&format!(" at {:?}", l)),
                    None => "".to_string(),
                };
                let color =
                    if location.is_some() || matches!(capability, Some(CapabilityKind::Write)) {
                        "gray"
                    } else {
                        "black"
                    };
                let region_html = match region {
                    Some(r) => format!("<br/>{}", r),
                    None => "".to_string(),
                };
                let label = format!(
                    "<FONT FACE=\"courier\">{}</FONT>&nbsp;{}{}{}",
                    escape_html(&label),
                    escape_html(&capability_text),
                    escape_html(&location_text),
                    region_html
                );
                DotNode {
                    id: self.id.to_string(),
                    label: DotLabel::Html(label),
                    color: DotStringAttr(color.to_string()),
                    font_color: DotStringAttr(color.to_string()),
                    shape: DotStringAttr("rect".to_string()),
                    style: None,
                    penwidth: None,
                }
            }
            NodeType::RegionProjectionNode { label } => DotNode {
                id: self.id.to_string(),
                label: DotLabel::Text(label.clone()),
                color: DotStringAttr("blue".to_string()),
                font_color: DotStringAttr("blue".to_string()),
                shape: DotStringAttr("octagon".to_string()),
                style: None,
                penwidth: None,
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NodeType {
    FPCSNode {
        label: String,
        capability: Option<CapabilityKind>,
        location: Option<Location>,
        region: Option<String>,
    },
    RegionProjectionNode {
        label: String,
    },
    ReborrowingDagNode {
        label: String,
        location: Option<Location>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ReferenceEdgeType {
    RustcBorrow(BorrowIndex, RegionVid),
    PCS,
}

impl std::fmt::Display for ReferenceEdgeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RustcBorrow(borrow_index, region_vid) => {
                write!(f, "{:?}: {:?}", borrow_index, region_vid)
            }
            Self::PCS => write!(f, "PCS"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum GraphEdge {
    AbstractEdge {
        blocked: NodeId,
        blocking: NodeId,
    },
    RegionBlockedByPlaceEdge {
        region: NodeId,
        place: NodeId,
    },
    RegionBlocksPlaceEdge {
        region: NodeId,
        place: NodeId,
    },
    BlocksAbstractionEdge {
        blocked_region: NodeId,
        blocking_region: NodeId,
    },
    UnblockReborrowEdge {
        blocked_place: NodeId,
        blocking_place: NodeId,
        block: BasicBlock,
        reason: String,
    },
    UnblockProjectionEdge {
        blocked_place: NodeId,
        blocking_place: NodeId,
        block: BasicBlock,
        reason: String,
    },
    ReborrowEdge {
        borrowed_place: NodeId,
        assigned_place: NodeId,
        location: Location,
        region: String,
        path_conditions: String,
    },
    ReferenceEdge {
        borrowed_place: NodeId,
        assigned_place: NodeId,
        edge_type: ReferenceEdgeType,
    },
    ProjectionEdge {
        source: NodeId,
        target: NodeId,
    },
    DerefExpansionEdge {
        source: NodeId,
        target: NodeId,
        location: Location,
    },
    RegionProjectionMemberEdge {
        place: NodeId,
        region_projection: NodeId,
    },
}

impl GraphEdge {
    fn to_dot_edge(&self) -> DotEdge {
        match self {
            GraphEdge::ReferenceEdge {
                borrowed_place,
                assigned_place,
                edge_type,
            } => DotEdge {
                from: borrowed_place.to_string(),
                to: assigned_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward)
                    .with_label(format!("{}", edge_type))
                    .with_style("dashed".to_string()),
            },
            GraphEdge::ProjectionEdge { source, target } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::undirected(),
            },
            GraphEdge::ReborrowEdge {
                borrowed_place,
                assigned_place,
                location: _,
                region,
                path_conditions,
            } => DotEdge {
                to: assigned_place.to_string(),
                from: borrowed_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward)
                    .with_color("orange".to_string())
                    .with_label(format!("{} - {}", region, path_conditions)),
            },
            GraphEdge::DerefExpansionEdge {
                source,
                target,
                location,
            } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::undirected()
                    .with_color("green".to_string())
                    .with_label(format!("{:?}", location)),
            },
            GraphEdge::UnblockReborrowEdge {
                blocked_place,
                blocking_place,
                block,
                reason,
            } => DotEdge {
                from: blocked_place.to_string(),
                to: blocking_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward)
                    .with_color("red".to_string())
                    .with_label(format!("{:?}({})", block, reason)),
            },
            GraphEdge::UnblockProjectionEdge {
                blocked_place,
                blocking_place,
                block,
                reason,
            } => DotEdge {
                from: blocked_place.to_string(),
                to: blocking_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("darkred".to_string())
                    .with_label(format!("{:?}({})", block, reason)),
            },
            GraphEdge::BlocksAbstractionEdge {
                blocked_region,
                blocking_region,
            } => DotEdge {
                from: blocked_region.to_string(),
                to: blocking_region.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward),
            },
            GraphEdge::RegionBlockedByPlaceEdge { region, place } => DotEdge {
                from: region.to_string(),
                to: place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward),
            },
            GraphEdge::RegionBlocksPlaceEdge { region, place } => DotEdge {
                from: place.to_string(),
                to: region.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward),
            },
            GraphEdge::AbstractEdge { blocked, blocking } => DotEdge {
                from: blocked.to_string(),
                to: blocking.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward),
            },
            GraphEdge::RegionProjectionMemberEdge {
                place: source,
                region_projection: target,
            } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Backward),
            },
        }
    }
}

pub struct Graph {
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
    clusters: HashSet<GraphCluster>,
}

impl Graph {
    fn new(
        nodes: Vec<GraphNode>,
        edges: HashSet<GraphEdge>,
        clusters: HashSet<GraphCluster>,
    ) -> Self {
        Self {
            nodes,
            edges,
            clusters,
        }
    }
}

pub fn generate_unblock_dot_graph<'a, 'tcx: 'a>(
    repacker: &PlaceRepacker<'a, 'tcx>,
    unblock_graph: &UnblockGraph<'tcx>,
) -> io::Result<String> {
    let constructor = UnblockGraphConstructor::new(unblock_graph.clone(), *repacker);
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub fn generate_dot_graph<'a, 'tcx: 'a>(
    _location: Location,
    repacker: PlaceRepacker<'a, 'tcx>,
    summary: &CapabilitySummary<'tcx>,
    borrows_domain: &BorrowsState<'a, 'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    _input_facts: &PoloniusInput,
    file_path: &str,
) -> io::Result<()> {
    let constructor = PCSGraphConstructor::new(summary, repacker, borrows_domain, borrow_set);
    let graph = constructor.construct_graph();
    let drawer = GraphDrawer::new(File::create(file_path).unwrap());
    drawer.draw(graph)
}
