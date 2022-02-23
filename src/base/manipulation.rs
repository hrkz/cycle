use crate::SymbolicResult;
use crate::{Edge, Expr, Tree};

#[derive(Debug, Clone)]
pub struct Evaluate {
  arg: Tree,
  mat: Tree,
  sub: Tree,
}

impl Expr for Evaluate {
  fn edge(self) -> Edge {
    Edge::from(self.trivial().unwrap_or(Tree::Form))
  }

  fn trivial(self) -> SymbolicResult<Tree> {
    // arg(mat -> sub)
    let mut arg = self.arg.trivial()?;
    arg.subs(
      &self.mat, // arg(sub)
      &self.sub,
    );
    arg.trivial()
  }

  fn visit<B, F>(
    //.
    &self,
    init: B,
    f: F,
  ) -> B
  where
    F: Fn(B, &Tree) -> B,
  {
    f(f(f(init, &self.arg), &self.mat), &self.sub)
  }
  fn visit_mut<F>(
    //.
    &mut self,
    _f: F,
  ) where
    F: Fn(&mut Tree),
  {
  }
}

#[derive(Debug, Clone)]
struct Expand {
  arg: Tree,
}

impl Expr for Expand {
  fn edge(self) -> Edge {
    Edge::from(self.trivial().unwrap_or(Tree::Form))
  }

  fn trivial(self) -> SymbolicResult<Tree> {
    self.expand_all()
  }

  fn visit<B, F>(
    //.
    &self,
    init: B,
    f: F,
  ) -> B
  where
    F: Fn(B, &Tree) -> B,
  {
    f(init, &self.arg)
  }
  fn visit_mut<F>(
    //.
    &mut self,
    f: F,
  ) where
    F: Fn(&mut Tree),
  {
    f(&mut self.arg);
  }
}

impl Expand {
  fn expand_all(self) -> SymbolicResult<Tree> {
    self.arg.trivial()
  }
}

impl Tree {
  pub(crate) fn evaluate(
    //.
    self,
    mat: Tree,
    sub: Tree,
  ) -> impl Expr {
    Evaluate { arg: self, mat, sub }
  }

  /// Expand products and positive integer powers.
  pub fn expand(self) -> impl Expr {
    Expand { arg: self }
  }
}
