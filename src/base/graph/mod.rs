#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct GraphBase<N, E> {
  nodes: Vec<N>,
  edges: Vec<E>,
}
