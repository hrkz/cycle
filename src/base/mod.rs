pub mod alg;
pub mod cal;
pub mod fun;
pub mod manipulation;
pub mod sq;

pub mod algebra;

pub mod array;
pub mod graph;

use std::any;
use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter;
use std::sync::Arc;

use algebra::{Constant, Form, Integer, Number, Rational, Structure, SymbolicResult};

pub use alg::{Algebra, Assoc};
pub use cal::Calculus;
pub use fun::{Function, Special};
pub use sq::Sequence;

/// An arbitrary variable.
#[derive(Debug, Clone, PartialOrd, Ord)]
pub struct Symbol {
  /// Name of the symbol.
  name: Arc<str>,
  /// Domain on which its structure applies.
  dom: Structure,
}

impl Symbol {
  /// Create a new symbol in a structure.
  pub fn new(name: &str, dom: Structure) -> Option<Symbol> {
    if name.contains(
      &[
        '#', '~', // special
        '+', '-', '*', '/', '^', // operators
        ' ', '=', ':', // control
        '(', ')', '{', '}', // syntax
      ][..],
    ) {
      None
    } else {
      Some(Symbol {
        // any indice-valid character
        name: Arc::from(name),
        dom,
      })
    }
  }
}

/// The expression tree.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Tree {
  /// An arbitrary variable.
  Sym(Symbol),
  /// Some selected mathematical constants.
  Cte(Constant),
  /// A countable number (excluding irrational and complex numbers).
  Num(Number),

  /// An algebraic operator.
  Alg(Algebra),
  /// A functional operator (elementary, special, arbitrary).
  Fun(Function),
  /// A calculus operator (derivative, integrals).
  Cal(Calculus),
  /// A sequential operator (sum, product).
  Sq(Sequence),
  /// A lazy indeterminate form.
  Form,
}

/// A recursive [`Tree`] expression.
pub type Edge = Arc<Tree>;

/// A marker trait for expression nodes.
pub trait Node: Sized {
  /// The associated node type.
  type Tree;
  /// The associated edge type.
  type Edge;
}

impl<T> Node for T
where
  T: Expr,
{
  type Tree = Tree;
  type Edge = Edge;
}

/// A trait for expression manipulation.
pub trait Expr: Sized {
  /// Retrieve expression name.
  fn name(&self) -> &str {
    any::type_name::<Self>()
  }

  /// Transform to a recursive [`Edge`] expression.
  fn edge(self) -> Edge;
  /// Apply trivial simplifications.
  fn trivial(self) -> SymbolicResult<Tree>;

  /// Visit the nodes of the expression tree.
  fn visit<B, F>(
    //.
    &self,
    init: B,
    f: F,
  ) -> B
  where
    F: Fn(B, &Tree) -> B;
  /// Visit the mutable nodes of the expression tree.
  fn visit_mut<F>(
    //.
    &mut self,
    f: F,
  ) where
    F: Fn(&mut Tree);

  /// ```a + b```
  fn add<T: Expr>(
    //.
    self,
    o: T,
  ) -> Tree {
    Tree::assoc(alg::AOp::Add, vec![self.edge(), o.edge()])
  }

  /// ```a*b```
  fn mul<T: Expr>(
    //.
    self,
    o: T,
  ) -> Tree {
    Tree::assoc(alg::AOp::Mul, vec![self.edge(), o.edge()])
  }

  /// ```-a = (-1)*a```
  fn neg(self) -> Tree {
    Tree::NEG_ONE.mul(self)
  }

  /// ```a - b = a + (-b)```
  fn sub<T: Expr>(
    //.
    self,
    o: T,
  ) -> Tree {
    self.add(o.neg())
  }

  /// ```a/b = a*b^-1```
  fn div<T: Expr>(
    //.
    self,
    o: T,
  ) -> Tree {
    self.mul(o.pow(Tree::NEG_ONE))
  }

  /// ```x!```
  fn fact(self) -> Tree {
    Tree::Alg(Algebra::UExpr {
      map: alg::UOp::Fact,
      arg: self.edge(),
    })
  }

  /// ```a^b```
  fn pow<T: Expr>(
    //.
    self,
    o: T,
  ) -> Tree {
    Tree::Alg(Algebra::BExpr {
      map: alg::BOp::Pow,
      arg: (self.edge(), o.edge()),
    })
  }

  /// ```b√a = a^(1/b)```
  fn root<T: Expr>(
    //.
    self,
    o: T,
  ) -> Tree {
    self.pow(Tree::ONE.div(o))
  }

  /// ```√a = a^(1/2)```
  fn sqrt(self) -> Tree {
    self.pow(Tree::HALF)
  }

  /// ```sin(x)```
  fn sin(self) -> Tree {
    Tree::elem(fun::EOp::Sin, self.edge())
  }
  /// ```cos(x)```
  fn cos(self) -> Tree {
    Tree::elem(fun::EOp::Cos, self.edge())
  }
  /// ```tan(x)```
  fn tan(self) -> Tree {
    Tree::elem(fun::EOp::Tan, self.edge())
  }

  /// ```arcsin(x)```
  fn arcsin(self) -> Tree {
    Tree::elem(fun::EOp::ArcSin, self.edge())
  }
  /// ```arccos(x)```
  fn arccos(self) -> Tree {
    Tree::elem(fun::EOp::ArcCos, self.edge())
  }
  /// ```arctan(x)```
  fn arctan(self) -> Tree {
    Tree::elem(fun::EOp::ArcTan, self.edge())
  }

  /// ```sinh(x)```
  fn sinh(self) -> Tree {
    Tree::elem(fun::EOp::Sinh, self.edge())
  }
  /// ```cosh(x)```
  fn cosh(self) -> Tree {
    Tree::elem(fun::EOp::Cosh, self.edge())
  }
  /// ```tanh(x)```
  fn tanh(self) -> Tree {
    Tree::elem(fun::EOp::Tanh, self.edge())
  }

  /// ```arsinh(x)```
  fn arsinh(self) -> Tree {
    Tree::elem(fun::EOp::ArSinh, self.edge())
  }
  /// ```arcosh(x)```
  fn arcosh(self) -> Tree {
    Tree::elem(fun::EOp::ArCosh, self.edge())
  }
  /// ```artanh(x)```
  fn artanh(self) -> Tree {
    Tree::elem(fun::EOp::ArTanh, self.edge())
  }

  /// ```exp(x)```
  fn exp(self) -> Tree {
    Tree::elem(fun::EOp::Exp, self.edge())
  }
  /// ```log(x)```
  fn log(self) -> Tree {
    Tree::elem(fun::EOp::Log, self.edge())
  }

  /// ```Γ(x)```
  fn gamma(self) -> Tree {
    Tree::Fun(Function::SpecExpr(Special::Gamma(self.edge())))
  }

  /// ```map(x_1, ..., x_n)```
  fn map(
    //.
    map: Symbol,
    arg: Vec<Tree>,
  ) -> Tree {
    Tree::Fun(Function::MapExpr { map, arg })
  }

  /// ```∂f/(∂x_1 ∂x_2 ... ∂x_n)```
  fn derivative(
    //.
    self,
    var: Vec<Symbol>,
  ) -> Tree {
    Tree::calculus_order(cal::CalOp::Der, self.edge(), var)
  }

  /// ```∫ ∫ ... ∫ f dx_1 dx_2 ... dx_n```
  fn integral(
    //.
    self,
    var: Vec<Symbol>,
  ) -> Tree {
    Tree::calculus_order(cal::CalOp::Int, self.edge(), var)
  }

  /// ```∑{i=l->u} f```
  fn sum<L, U>(
    //.
    self,
    idx: Symbol,
    lo: L,
    up: U,
  ) -> Tree
  where
    L: Expr,
    U: Expr,
  {
    Tree::sequence_order(sq::SqOp::Sum, idx, lo.edge(), up.edge(), self.edge())
  }

  /// ```∏{i=l->u} f```
  fn product<L, U>(
    //.
    self,
    idx: Symbol,
    lo: L,
    up: U,
  ) -> Tree
  where
    L: Expr,
    U: Expr,
  {
    Tree::sequence_order(sq::SqOp::Prod, idx, lo.edge(), up.edge(), self.edge())
  }

  /// Transform the expression to a nontrivial one (which can't be simplified).
  fn nontrivial(self) -> Tree {
    let name = if let Some(name) = self.name().split("::").last() { name } else { self.name() };

    let map = Symbol::new(name, Structure::AS).expect("incorrect expression name");
    let arg = self.visit(Vec::new(), |mut acc, e| {
      acc.push(e.clone());
      acc
    });

    Tree::map(
      map, //.
      arg,
    )
  }
}

impl<T> Expr for T
where
  T: Borrow<Tree> + BorrowMut<Tree>,
  T: Into<Edge>,
  T: Into<Tree>,
{
  fn edge(self) -> Edge {
    self.into()
  }

  fn trivial(self) -> SymbolicResult<Tree> {
    let tree = self.into();
    match tree {
      Tree::Form => Err(Form {}),
      Tree::Sym(_) | Tree::Cte(_) => Ok(
        tree, //.
      ),
      Tree::Num(
        n, //.
      ) => Ok(Tree::Num(n.trivial()?)),

      Tree::Alg(
        a, //.
      ) => a.alg_trivial(),
      Tree::Fun(
        f, //.
      ) => f.fun_trivial(),
      Tree::Cal(
        c, //.
      ) => c.cal_trivial(),
      Tree::Sq(
        s, //.
      ) => s.sq_trivial(),
    }
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
    match self.borrow() {
      Tree::Alg(alg) => {
        match alg {
          Algebra::UExpr {
            // 1
            map: _,
            arg,
          } => f(init, arg),

          Algebra::BExpr {
            // 2
            map: _,
            arg,
          } => f(f(init, &arg.0), &arg.1),

          Algebra::AssocExpr(Assoc {
            // n
            map: _,
            arg,
          }) => {
            arg.iter().fold(
              init, //.
              |acc, e| f(acc, e),
            )
          }
        }
      }

      Tree::Fun(fun) => {
        match fun {
          Function::ElemExpr {
            // 1
            map: _,
            arg,
          } => f(init, arg),

          Function::SpecExpr(
            // n
            map,
          ) => match map {
            Special::Gamma(arg) => f(init, arg),
          },

          Function::MapExpr {
            // n
            map: _,
            arg,
          } => {
            arg.iter().fold(
              init, //.
              f,
            )
          }
        }
      }

      Tree::Sq(sq) => f(f(f(init, &sq.arg), &sq.lo), &sq.up),
      // change
      Tree::Cal(_) => init,

      lit => {
        f(
          init, //.
          lit,
        )
      }
    }
  }

  fn visit_mut<F>(
    //.
    &mut self,
    f: F,
  ) where
    F: Fn(&mut Tree),
  {
    match self.borrow_mut() {
      Tree::Alg(alg) => {
        match alg {
          Algebra::UExpr {
            // 1
            map: _,
            arg,
          } => f(arg.borrow_mut()),

          Algebra::BExpr {
            // 2
            map: _,
            arg,
          } => {
            f(arg.0.borrow_mut());
            f(arg.1.borrow_mut());
          }

          Algebra::AssocExpr(Assoc {
            // n
            map: _,
            arg,
          }) => {
            arg.iter_mut().for_each(
              |e| f(e.borrow_mut()), //.
            )
          }
        }
      }

      Tree::Fun(fun) => {
        match fun {
          Function::ElemExpr {
            // 1
            map: _,
            arg,
          } => f(arg.borrow_mut()),

          Function::SpecExpr(
            // n
            map,
          ) => match map {
            Special::Gamma(arg) => f(arg.borrow_mut()),
          },

          Function::MapExpr {
            // n
            map: _,
            arg,
          } => {
            arg.iter_mut().for_each(
              f, //.
            )
          }
        }
      }

      Tree::Sq(sq) => {
        f(sq.arg.borrow_mut());
        f(sq.lo.borrow_mut());
        f(sq.up.borrow_mut());
      }

      // change
      Tree::Cal(_) => {}

      lit => {
        f(lit) //.
      }
    }
  }
}

impl Tree {
  pub const ZERO: Tree = Tree::Num(Number::Z(0));
  pub const ONE: Tree = Tree::Num(Number::Z(1));
  pub const NEG_ONE: Tree = Tree::Num(Number::Z(-1));
  pub const HALF: Tree = Tree::Num(Number::Q(Rational::new(1, 2)));
  pub const QUARTER: Tree = Tree::Num(Number::Q(Rational::new(1, 4)));

  pub const MAP_PREC: u64 = 5;

  /// Determine the applying domain.
  pub fn dom(&self) -> Structure {
    match self {
      Tree::Sym(s) => s.dom,
      Tree::Cte(c) => c.dom(),
      Tree::Num(n) => n.dom(),
      Tree::Form //.rec
    | Tree::Alg(_)
    | Tree::Fun(_)
    | Tree::Cal(_)
    | Tree::Sq(_) => {
        self.iter().fold(Structure::AS, |acc, e| acc.max(e.dom()))
      }
    }
  }

  /// Test if the expression is free of expression `expr`.
  pub fn free(&self, expr: &Tree) -> bool {
    if self.eq(expr) {
      return false;
    }

    match self {
      Tree::Form | Tree::Cte(_) | Tree::Sym(_) | Tree::Num(_) => true,
      Tree::Alg(_) //.rec
    | Tree::Fun(_)
    | Tree::Cal(_)
    | Tree::Sq(_) => {
        self.iter().fold(true, |acc, e| acc && e.free(expr))
      }
    }
  }

  /// Substitute in-place expression `expr` by `replace`.
  pub fn subs(&mut self, expr: &Tree, replace: &Tree) -> &mut Self {
    if expr.eq(self) {
      *self = replace.clone();
    } else if self.free(expr) {
      *self = self.clone();
    } else {
      match self {
        Tree::Form | Tree::Cte(_) | Tree::Sym(_) | Tree::Num(_) => *self = replace.clone(),
        Tree::Alg(_) //.rec
      | Tree::Fun(_)
      | Tree::Cal(_)
      | Tree::Sq(_) => {
          self.iter_mut().for_each(|e| {
            e.subs(
              expr, //.
              replace,
            );
          })
        }
      }
    }
    self
  }

  /// Check if the current expression is a litteral.
  pub fn is_literal(&self) -> bool {
    match self {
      Tree::Form | Tree::Sym(_) | Tree::Cte(_) | Tree::Num(_) => true,
      Tree::Alg(_) //.rec
    | Tree::Fun(_)
    | Tree::Cal(_)
    | Tree::Sq(_) => {
        false
      }
    }
  }

  /// Check if the current expression is a value (as opposed to symbol).
  pub fn is_value(&self) -> bool {
    matches!(self, Tree::Num(_))
  }

  /// Return a recursive iterator over the expression tree.
  /// * `fold_{self, rec}`
  /// * `any`
  pub fn iter(&self) -> Iter {
    Iter { root: self }
  }

  /// Return a mutable recursive iterator over the expression tree.
  /// * `for_each`
  pub fn iter_mut(&mut self) -> IterMut {
    IterMut { root: self }
  }

  // Helpers
  pub fn helper_len(&self) -> u64 {
    match self {
      Tree::Form => 0,
      Tree::Sym(_) | Tree::Cte(_) => 1,
      Tree::Num(n) => n.helper_len(),
      Tree::Alg(_) //.rec
    | Tree::Fun(_)
    | Tree::Cal(_)
    | Tree::Sq(_) => {
        self.iter().fold(0, |acc, e| acc + e.helper_len())
      }
    }
  }

  pub fn helper_prec(&self) -> u64 {
    match self {
      Tree::Sym(_) | Tree::Cte(_) => 0,
      Tree::Num(n) => n.helper_len(),
      Tree::Alg(a) => a.helper_prec(),
      Tree::Form //.rec
    | Tree::Fun(_)
    | Tree::Cal(_)
    | Tree::Sq(_) => {
        Tree::MAP_PREC
      }
    }
  }
}

impl PartialOrd for Tree {
  fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
    Some(self.cmp(o))
  }
}

impl Ord for Tree {
  fn cmp(&self, o: &Self) -> Ordering {
    match (self, o) {
      (Tree::Num(l), Tree::Num(r)) => l.cmp(r),
      (Tree::Sym(l), Tree::Sym(r)) => l.cmp(r),

      (
        Tree::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: lhs_map,
          arg: lhs,
        })),
        Tree::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: rhs_map,
          arg: rhs,
        })),
      ) => rhs_map.cmp(lhs_map).then(algebra::poly::order_expr(lhs.iter().map(|l| l.as_ref()), rhs.iter().map(|r| r.as_ref()))),

      (
        Tree::Alg(Algebra::BExpr {
          //.
          map: _,
          arg: (lhs_term, lhs_exp),
        }),
        Tree::Alg(Algebra::BExpr {
          //.
          map: _,
          arg: (rhs_term, rhs_exp),
        }),
      ) => lhs_term.cmp(rhs_term).then(rhs_exp.cmp(lhs_exp)),

      (
        Tree::Alg(Algebra::UExpr {
          //.
          map: _,
          arg: lhs,
        }),
        Tree::Alg(Algebra::UExpr {
          //.
          map: _,
          arg: rhs,
        }),
      ) => lhs.cmp(rhs),

      (
        Tree::Fun(Function::ElemExpr {
          //.
          map: lhs_map,
          arg: lhs_arg,
        }),
        Tree::Fun(Function::ElemExpr {
          //.
          map: rhs_map,
          arg: rhs_arg,
        }),
      ) => lhs_map.cmp(rhs_map).then(lhs_arg.cmp(rhs_arg)),

      (
        Tree::Fun(Function::MapExpr {
          //.
          map: lhs_map,
          arg: lhs_arg,
        }),
        Tree::Fun(Function::MapExpr {
          //.
          map: rhs_map,
          arg: rhs_arg,
        }),
      ) => lhs_map.cmp(rhs_map).then(lhs_arg.iter().cmp(rhs_arg.iter())),

      (Tree::Alg(Algebra::AssocExpr(Assoc { map: lhs_map, arg: lhs })), rhs) => lhs_map.cmp_poly(algebra::poly::order_expr(lhs.iter().map(|l| l.as_ref()), iter::once(rhs)), Ordering::Greater),
      (lhs, Tree::Alg(Algebra::AssocExpr(Assoc { map: rhs_map, arg: rhs }))) => rhs_map.cmp_poly(algebra::poly::order_expr(iter::once(lhs), rhs.iter().map(|r| r.as_ref())), Ordering::Less),

      (Tree::Alg(Algebra::BExpr { map: _, arg: (term, exp) }), rhs) => term.as_ref().cmp(rhs).then(Tree::ONE.cmp(exp.as_ref())),
      (lhs, Tree::Alg(Algebra::BExpr { map: _, arg: (term, exp) })) => lhs.cmp(term.as_ref()).then(exp.as_ref().cmp(&Tree::ONE)),

      (Tree::Cte(_), Tree::Sym(_)) => Ordering::Less,
      (Tree::Sym(_), Tree::Cte(_)) => Ordering::Greater,

      (Tree::Cte(_), Tree::Num(_)) => Ordering::Greater,
      (Tree::Num(_), Tree::Cte(_)) => Ordering::Less,

      (Tree::Sym(_), _) => Ordering::Less,
      (_, Tree::Sym(_)) => Ordering::Greater,

      _ => Ordering::Equal,
    }
  }
}

/// A recursive expression tree visitor.
pub struct Iter<'v> {
  root: &'v Tree,
}

impl<'v> Iter<'v> {
  pub fn fold<B, F>(
    //.
    &self,
    init: B,
    f: F,
  ) -> B
  where
    F: Fn(B, &Tree) -> B,
  {
    self.root.visit(init, f)
  }

  pub fn fold_self<B, F>(
    //.
    self,
    init: B,
    f: F,
  ) -> B
  where
    F: Fn(B, &Tree) -> B,
  {
    self.fold(f(init, self.root), f)
  }

  pub fn fold_rec<B, F>(
    //.
    self,
    init: B,
    f: &F,
  ) -> B
  where
    F: Fn(B, &Tree) -> B,
  {
    let init = f(init, self.root);

    if self.root.is_literal() {
      init
    } else {
      self.fold(
        init, //.
        |acc, e| e.iter().fold_rec(acc, f),
      )
    }
  }

  pub fn any<F>(
    //.
    self,
    f: &F,
  ) -> bool
  where
    F: Fn(&Tree) -> bool,
  {
    let init = f(self.root);
    if init {
      return true;
    }

    if self.root.is_literal() {
      init
    } else {
      self.fold(
        init, //.
        |acc, e| acc || e.iter().any(f),
      )
    }
  }
}

/// A recursive mutable expression tree visitor.
pub struct IterMut<'v> {
  root: &'v mut Tree,
}

impl<'v> IterMut<'v> {
  pub fn for_each<F>(
    //.
    self,
    f: F,
  ) where
    F: Fn(&mut Tree),
  {
    self.root.visit_mut(f)
  }
}

// Utility traits

impl Eq for Symbol {}
impl PartialEq for Symbol {
  fn eq(&self, o: &Self) -> bool {
    self.name.eq(&o.name)
  }
}

impl Hash for Symbol {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
  }
}

impl fmt::Display for Symbol {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.name)
  }
}

impl fmt::Display for Tree {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(
      match self.borrow() {
        Tree::Form => &Form {} as &dyn fmt::Display,
        Tree::Sym(s) => s,
        Tree::Cte(c) => c,
        Tree::Num(
          n, //.
        ) => n,

        Tree::Alg(
          a, //.
        ) => a,
        Tree::Fun(
          f, //.
        ) => f,
        Tree::Cal(
          c, //.
        ) => c,
        Tree::Sq(
          s, //.
        ) => s,
      },
      f,
    )
  }
}

// Conversions

impl BorrowMut<Tree> for Edge {
  fn borrow_mut(&mut self) -> &mut Tree {
    Arc::make_mut(self)
  }
}

impl TryFrom<Tree> for Symbol {
  type Error = Form;

  fn try_from(tree: Tree) -> Result<Self, Self::Error> {
    if let Tree::Sym(symbol) = tree {
      Ok(symbol)
    } else {
      Err(
        Form {}, //.
      )
    }
  }
}

impl From<Integer> for Tree {
  fn from(z: Integer) -> Self {
    Tree::Num(Number::Z(z))
  }
}

impl From<Rational> for Tree {
  fn from(q: Rational) -> Self {
    Tree::Num(Number::Q(q))
  }
}

impl From<Edge> for Tree {
  #[inline]
  fn from(edge: Edge) -> Tree {
    (*edge).clone()
  }
}

impl From<&Edge> for Tree {
  #[inline]
  fn from(edge: &Edge) -> Tree {
    (**edge).clone()
  }
}
