//! Array manipulation for both symbolic and numerical problems.

use std::sync::Arc;

/// The base generic array.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ArrayBase<S, D> {
  data: Arc<S>,
  dims: D,
}
