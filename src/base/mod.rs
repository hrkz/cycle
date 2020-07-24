pub mod alg;
pub mod ring;

use std::rc::Rc;

use alg::Algebra;
use ring::{Constant, Number, Ring, SymbolicResult};

#[derive(Debug, Clone)]
pub struct Symbol {
  name: String,
  ring: Ring,
}

#[derive(Debug, Clone)]
pub enum Expr {
  SymExpr(Rc<Symbol>),
  CteExpr(Rc<Constant>),

  NumExpr(Number),

  AlgExpr(Algebra),
  //CalExpr(Calculus),
  //SeqExpr(Sequence)
}

impl Expr {
  pub fn trivial(self) -> SymbolicResult<Expr> { Ok(self) }
}
