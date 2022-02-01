//! Graph manipulation for discrete mathematics problems.

/// The base generic graph.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct GraphBase<N, E> {
  nodes: Vec<N>,
  edges: Vec<E>,
}
