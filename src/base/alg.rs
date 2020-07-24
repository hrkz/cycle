use crate::base::Expr;

#[derive(Debug, Clone)]
pub enum UOp {
  Elem,
  Fact,
}

#[derive(Debug, Clone)]
pub enum BOp {
  Pow,
  Mod,
}

#[derive(Debug, Clone)]
pub enum FieldOp {
  Add,
  Mul,
}

#[derive(Debug, Clone)]
pub enum Algebra {
  UExpr {
    map: UOp,
    arg: Box<Expr>,
  },

  BExpr {
    map: BOp,
    arg: (Box<Expr>, Box<Expr>),
  },

  FieldExpr(
    //.
    Field,
  ),
}

#[derive(Debug, Clone)]
pub struct Field {
  pub map: FieldOp,
  pub arg: Vec<Expr>,
}
