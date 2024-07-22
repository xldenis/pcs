use std::{
    fs::File,
    io::{self, Write},
};

use crate::{free_pcs::CapabilityKind, visualization::dot_graph::DotGraph};

use super::{
    dot_graph::{DotLabel, DotNode},
    Graph, GraphDrawer, GraphEdge, GraphNode, NodeId, NodeType,
};

impl<T: io::Write> GraphDrawer<T> {
    pub fn new(out: T) -> Self {
        Self { out }
    }

    pub fn draw(mut self, graph: Graph) -> io::Result<()> {
        let dot_graph = DotGraph {
            name: "CapabilitySummary".to_string(),
            nodes: graph.nodes.into_iter().map(|g| g.to_dot_node()).collect(),
            edges: graph.edges.into_iter().map(|e| e.to_dot_edge()).collect(),
            subgraphs: vec![]
        };
        writeln!(self.out, "{}", dot_graph)
    }
}
