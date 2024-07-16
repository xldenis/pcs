use std::{
    fs::File,
    io::{self, Write},
};

use super::{Graph, GraphDrawer, GraphEdge, GraphNode, NodeId, NodeType};

pub struct EdgeOptions {
    label: String,
    color: Option<String>,
    style: Option<String>,
    directed: bool,
}

impl EdgeOptions {
    pub fn new() -> Self {
        Self {
            label: "".to_string(),
            color: None,
            style: None,
            directed: true,
        }
    }

    pub fn with_label(mut self, label: String) -> Self {
        self.label = label;
        self
    }

    pub fn with_color(mut self, color: String) -> Self {
        self.color = Some(color);
        self
    }

    pub fn with_style(mut self, style: String) -> Self {
        self.style = Some(style);
        self
    }

    pub fn directed(mut self, directed: bool) -> Self {
        self.directed = directed;
        self
    }
}

impl<T: io::Write> GraphDrawer<T> {
    pub fn new(out: T) -> Self {
        Self { out }
    }

    pub fn draw(mut self, graph: Graph) -> io::Result<()> {
        writeln!(self.out, "digraph CapabilitySummary {{")?;
        writeln!(self.out, "node [shape=rect]")?;
        for node in graph.nodes {
            self.draw_node(node)?;
        }
        for edge in graph.edges {
            self.draw_edge(edge)?;
        }
        writeln!(&mut self.out, "}}")
    }

    fn escape_html(input: String) -> String {
        input
            .replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace("\"", "&quot;")
            .replace("'", "&#39;")
    }

    fn draw_node(&mut self, node: GraphNode) -> io::Result<()> {
        match node.node_type {
            NodeType::PlaceNode {
                capability,
                label,
                location,
            } => {
                let (capability_text, color) = match capability {
                    Some(k) => (format!("{:?}", k), "black"),
                    None => ("N".to_string(), "gray"),
                };
                let location_text = match location {
                    Some(l) => Self::escape_html(format!("@{:?}", l)),
                    None => "".to_string(),
                };
                writeln!(
                    self.out,
                    "    \"{}\" [label=<<FONT FACE=\"courier\">{}</FONT>&nbsp;{}{}>, fontcolor=\"{}\", color=\"{}\"];",
                    node.id, Self::escape_html(label), Self::escape_html(capability_text), location_text, color, color
                )?;
            }
        }
        Ok(())
    }

    fn draw_dot_edge(
        &mut self,
        source: NodeId,
        target: NodeId,
        options: EdgeOptions,
    ) -> io::Result<()> {
        let style_part = match options.style {
            Some(style) => format!(", style=\"{}\"", style),
            None => "".to_string(),
        };
        let arrowhead_part = if !options.directed {
            ", arrowhead=\"none\""
        } else {
            ""
        };
        let color_part = match options.color {
            Some(color) => format!(", color=\"{}\"", color),
            None => "".to_string(),
        };

        writeln!(
            self.out,
            "    \"{}\" -> \"{}\" [label=\"{}\"{}{}{}]",
            source, target, options.label, style_part, arrowhead_part, color_part
        )
    }

    fn draw_edge(&mut self, edge: GraphEdge) -> io::Result<()> {
        match edge {
            GraphEdge::ReferenceEdge {
                borrowed_place,
                assigned_place,
                edge_type,
            } => {
                self.draw_dot_edge(
                    borrowed_place,
                    assigned_place,
                    EdgeOptions::new()
                        .with_label(format!("{}", edge_type))
                        .with_style("dashed".to_string())
                        .directed(true),
                )?;
            }
            GraphEdge::ProjectionEdge { source, target } => {
                self.draw_dot_edge(source, target, EdgeOptions::new().directed(false))?;
            }
            GraphEdge::ReborrowEdge {
                borrowed_place,
                assigned_place,
                location,
            } => {
                self.draw_dot_edge(
                    assigned_place,
                    borrowed_place,
                    EdgeOptions::new()
                        .with_color("orange".to_string())
                        .with_label(format!("{:?}", location))
                        .directed(true),
                )?;
            }
            GraphEdge::DerefExpansionEdge {
                source,
                target,
                block,
            } => {
                self.draw_dot_edge(
                    source,
                    target,
                    EdgeOptions::new()
                        .with_color("green".to_string())
                        .with_label(format!("{:?}", block))
                        .directed(false),
                )?;
            }
            GraphEdge::UnblockReborrowEdge {
                blocked_place,
                blocking_place,
                block
            } => {
                self.draw_dot_edge(
                    blocked_place,
                    blocking_place,
                    EdgeOptions::new()
                        .with_color("red".to_string())
                        .with_label(format!("{:?}", block)),
                )?;
            }
            GraphEdge::UnblockProjectionEdge {
                blocked_place,
                blocking_place,
                block
            } => {
                self.draw_dot_edge(
                    blocked_place,
                    blocking_place,
                    EdgeOptions::new()
                        .with_color("darkred".to_string())
                        .with_label(format!("{:?}", block)),
                )?;
            }
        }
        Ok(())
    }
}
