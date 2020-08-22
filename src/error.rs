use std::fmt;

#[derive(Debug)]
pub enum PredecessorError {
    EmptyGraph,
    NotTreeEdges,
}

impl fmt::Display for PredecessorError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PredecessorError::EmptyGraph => write!(f, "The graph has no vertex."),
            PredecessorError::NotTreeEdges => write!(f, "The edges do not build a tree."),
        }
    }
}
