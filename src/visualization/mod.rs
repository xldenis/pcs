// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod drawer;
pub mod graph_constructor;
pub mod mir_graph;

use crate::{
    borrows::domain::{
        Borrow, BorrowsState, MaybeOldPlace, PlaceSnapshot, RegionAbstraction,
    },
    combined_pcs::UnblockGraph,
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker},
};
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
            self, BasicBlock, Body, Local, Location, PlaceElem, Promoted, TerminatorKind,
            UnwindAction, VarDebugInfo, RETURN_PLACE,
        },
        ty::{self, GenericArgsRef, ParamEnv, RegionVid, TyCtxt},
    },
};

use self::graph_constructor::{PCSGraphConstructor, UnblockGraphConstructor};

pub fn place_id<'tcx>(place: &Place<'tcx>) -> String {
    format!("{:?}", place)
}

struct GraphDrawer<T: io::Write> {
    out: T,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct NodeId(usize);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "n{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct GraphNode {
    id: NodeId,
    node_type: NodeType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NodeType {
    PlaceNode {
        label: String,
        capability: Option<CapabilityKind>,
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
    UnblockReborrowEdge {
        blocked_place: NodeId,
        blocking_place: NodeId,
    },
    ReborrowEdge {
        borrowed_place: NodeId,
        assigned_place: NodeId,
        location: Location,
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
        block: BasicBlock,
    },
}

pub struct Graph {
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
}

impl Graph {
    fn new(nodes: Vec<GraphNode>, edges: HashSet<GraphEdge>) -> Self {
        Self { nodes, edges }
    }
}

pub fn get_source_name_from_local(local: &Local, debug_info: &[VarDebugInfo]) -> Option<String> {
    if local.as_usize() == 0 {
        return None;
    }
    debug_info.get(&local.as_usize() - 1).map(|source_info| {
        let name = source_info.name.as_str();
        let mut shadow_count = 0;
        for i in 0..local.as_usize() - 1 {
            if debug_info[i].name.as_str() == name {
                shadow_count += 1;
            }
        }
        if shadow_count == 0 {
            format!("{}", name)
        } else {
            format!("{}$shadow{}", name, shadow_count)
        }
    })
}

pub fn get_source_name_from_place<'tcx>(
    local: Local,
    projection: &[PlaceElem<'tcx>],
    debug_info: &[VarDebugInfo],
) -> Option<String> {
    get_source_name_from_local(&local, debug_info).map(|mut name| {
        let mut iter = projection.iter().peekable();
        while let Some(elem) = iter.next() {
            match elem {
                mir::ProjectionElem::Deref => {
                    if iter.peek().is_some() {
                        name = format!("(*{})", name);
                    } else {
                        name = format!("*{}", name);
                    }
                }
                mir::ProjectionElem::Field(field, _) => {
                    name = format!("{}.{}", name, field.as_usize());
                }
                mir::ProjectionElem::Index(_) => todo!(),
                mir::ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                mir::ProjectionElem::Subslice { from, to, from_end } => todo!(),
                mir::ProjectionElem::Downcast(d, v) => {
                    name = format!("downcast {:?} as {:?}", name, d);
                }
                mir::ProjectionElem::OpaqueCast(_) => todo!(),
            }
        }
        name
    })
}

pub fn generate_unblock_dot_graph<'a, 'tcx: 'a>(
    repacker: &PlaceRepacker<'a, 'tcx>,
    unblock_graph: &UnblockGraph<'tcx>,
) -> io::Result<String> {
    let constructor = UnblockGraphConstructor::new(unblock_graph.clone(), *repacker);
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let mut drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub fn generate_dot_graph<'a, 'tcx: 'a>(
    location: Location,
    repacker: PlaceRepacker<'a, 'tcx>,
    summary: &CapabilitySummary<'tcx>,
    borrows_domain: &BorrowsState<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    input_facts: &PoloniusInput,
    file_path: &str,
) -> io::Result<()> {
    let constructor = PCSGraphConstructor::new(summary, repacker, borrows_domain, borrow_set);
    let graph = constructor.construct_graph();
    let mut drawer = GraphDrawer::new(File::create(file_path).unwrap());
    drawer.draw(graph)

    // for (idx, region_abstraction) in borrows_domain.region_abstractions.iter().enumerate() {
    //     let ra_node_label = format!("ra{}", idx);
    //     writeln!(
    //         drawer.file,
    //         "    \"{}\" [label=\"{}\", shape=egg];",
    //         ra_node_label, ra_node_label
    //     )?;
    //     for loan_in in &region_abstraction.loans_in {
    //         drawer.add_place_if_necessary((*loan_in).into())?;
    //         dot_edge(
    //             &mut drawer.file,
    //             &place_id(&(*loan_in).into()),
    //             &ra_node_label,
    //             "loan_in",
    //             false,
    //         )?;
    //     }
    //     for loan_out in &region_abstraction.loans_out {
    //         drawer.add_place_if_necessary((*loan_out).into())?;
    //         dot_edge(
    //             &mut drawer.file,
    //             &ra_node_label,
    //             &place_id(&(*loan_out).into()),
    //             "loan_out",
    //             false,
    //         )?;
    //     }
    // }
}
