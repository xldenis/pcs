use std::collections::BTreeSet;

use crate::rustc_interface::{
    data_structures::graph::dominators::Dominators,
    middle::mir::{BasicBlock, BasicBlocks},
};

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct PathCondition {
    pub from: BasicBlock,
    pub to: BasicBlock,
}

impl PathCondition {
    pub fn new(from: BasicBlock, to: BasicBlock) -> Self {
        Self { from, to }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct Path(Vec<BasicBlock>);

impl Path {
    pub fn new(block: BasicBlock) -> Self {
        Self(vec![block])
    }

    pub fn append(&mut self, block: BasicBlock) {
        self.0.push(block);
    }

    pub fn start(&self) -> BasicBlock {
        self.0[0]
    }

    pub fn end(&self) -> BasicBlock {
        self.0[self.0.len() - 1]
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct PCGraph(BTreeSet<PathCondition>);

impl std::fmt::Display for PCGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for pc in self.0.iter() {
            write!(f, "{:?} -> {:?},", pc.from, pc.to)?;
        }
        Ok(())
    }
}

impl PCGraph {
    pub fn singleton(pc: PathCondition) -> Self {
        Self(BTreeSet::from([pc]))
    }

    pub fn has_path_to_block(&self, block: BasicBlock) -> bool {
        self.0.iter().any(|pc| pc.to == block)
    }

    pub fn insert(&mut self, pc: PathCondition) -> bool {
        if self.has_path_to_block(pc.to) {
            self.0.insert(pc)
        } else {
            false
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub enum PathConditions {
    AtBlock(BasicBlock),
    Paths(PCGraph),
}

impl std::fmt::Display for PathConditions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathConditions::AtBlock(b) => write!(f, "{:?}", b),
            PathConditions::Paths(p) => write!(f, "{}", p),
        }
    }
}

impl PathConditions {
    pub fn new(block: BasicBlock) -> Self {
        Self::AtBlock(block)
    }

    pub fn insert(&mut self, pc: PathCondition) -> bool {
        match self {
            PathConditions::AtBlock(b) => {
                if *b == pc.from {
                    *self = PathConditions::Paths(PCGraph::singleton(pc));
                    true
                } else {
                    eprintln!("Ignore {:?} for {:?}", pc, b);
                    false
                }
            }
            PathConditions::Paths(p) => p.insert(pc),
        }
    }
}
