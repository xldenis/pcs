use std::fmt::Display;

type NodeId = String;

pub struct DotGraph {
    pub name: String,
    pub nodes: Vec<DotNode>,
    pub edges: Vec<DotEdge>,
    pub subgraphs: Vec<DotSubgraph>,
}

impl DotGraph {
    pub fn write_to_file(&self, path: &str) -> std::io::Result<()> {
        std::fs::write(path, self.to_string())
    }
}

pub struct DotSubgraph {
    pub name: String,
    pub label: String,
    pub nodes: Vec<DotNode>,
}

impl Display for DotSubgraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "subgraph {} {{", self.name)?;
        writeln!(f, "label=\"{}\";", self.label)?;
        for node in &self.nodes {
            writeln!(f, "{}", node)?;
        }
        writeln!(f, "}}")
    }
}

impl Display for DotGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "digraph {} {{", self.name)?;
        writeln!(f, "node [shape=rect]")?;
        for node in &self.nodes {
            writeln!(f, "{}", node)?;
        }
        for edge in &self.edges {
            writeln!(f, "{}", edge)?;
        }
        for subgraph in &self.subgraphs {
            writeln!(f, "{}", subgraph)?;
        }
        writeln!(f, "}}")
    }
}

pub enum DotLabel {
    Text(String),
    Html(String),
}

impl Display for DotLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DotLabel::Text(text) => write!(f, "\"{}\"", text),
            DotLabel::Html(html) => write!(f, "<{}>", html),
        }
    }
}

pub struct DotNode {
    pub id: NodeId,
    pub label: DotLabel,
    pub font_color: String,
    pub color: String,
}

impl Display for DotNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "\"{}\" [label={}, fontcolor=\"{}\", color=\"{}\"];",
            self.id, self.label, self.font_color, self.color
        )
    }
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub struct EdgeOptions {
    label: String,
    color: Option<String>,
    style: Option<String>,
    directed: bool,
}

impl EdgeOptions {
    pub fn directed() -> Self {
        Self {
            label: "".to_string(),
            color: None,
            style: None,
            directed: true,
        }
    }

    pub fn undirected() -> Self {
        Self {
            label: "".to_string(),
            color: None,
            style: None,
            directed: false,
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
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub struct DotEdge {
    pub from: NodeId,
    pub to: NodeId,
    pub options: EdgeOptions,
}

impl Display for DotEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let style_part = match &self.options.style {
            Some(style) => format!(", style=\"{}\"", style),
            None => "".to_string(),
        };
        let arrowhead_part = if !self.options.directed {
            ", arrowhead=\"none\""
        } else {
            ""
        };
        let color_part = match &self.options.color {
            Some(color) => format!(", color=\"{}\"", color),
            None => "".to_string(),
        };

        write!(
            f,
            "    \"{}\" -> \"{}\" [label=\"{}\"{}{}{}]",
            self.from, self.to, self.options.label, style_part, arrowhead_part, color_part
        )
    }
}
