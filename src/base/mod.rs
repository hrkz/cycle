pub mod alg;
pub mod ring;

use std::cmp::Ordering;
use std::fmt;
use std::iter;
use std::ops;
use std::sync::Arc;

use alg::{Algebra, Assoc};
use ring::{Constant, Number, Set, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub struct Symbol {
  name: String,
  dom: Set,
}

impl Symbol {
  pub fn new(name_str: &str, dom: Set) -> Arc<Symbol> {
    let name = name_str.replace(&[' ', '+', '-', '*', '/', '^', '=', '(', ')', '{', '}', '#', '~'][..], "");
    // any non-whitespace, non-special character
    assert_eq!(name, name_str);

    Arc::new(Symbol {
      // extension to other formattings
      name,
      dom,
    })
  }
}

impl fmt::Display for Symbol {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.name) }
}

macro_rules!
match_term {
  ($m:expr ,{
    $(
      $($v:path)|* =>
        |$i:pat| $a:expr
     ),*
  }) => {
    match $m {
      $(
      $(
        $v($i) => {
          $a
        }
      ),*
      ),*
    }
  }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr {
  /// Symbol (variable) on a ring
  Sym(Arc<Symbol>),
  /// Special constant
  Cte(Arc<Constant>),

  /// Exact number
  Num(Number),

  /// Algebraic operation
  Alg(Algebra),
  // Calculus operation (limit, derivative, integral)
  //Cal(Calculus),
  // Sequence operation (sum, product)
  //Sq(Sequence),
}

impl Expr {
  pub const ZERO: Expr = Expr::Num(Number::Z(0));
  pub const ONE: Expr = Expr::Num(Number::Z(1));
  pub const NEG_ONE: Expr = Expr::Num(Number::Z(-1));

  pub fn trivial(self) -> SymbolicResult<Expr> {
    match_term!(
      self, {
        Expr::Sym
      | Expr::Cte => |_| Ok(self),
        Expr::Num => |n| Ok(Expr::Num(n.trivial()?)),
        Expr::Alg
    //| Expr::Cal
    //| Expr::Sq
        => |e| {
          e.trivial()
        }
      }
    )
  }

  pub fn len(&self) -> u64 {
    match self {
      Expr::Cte(_)
    | Expr::Sym(_) => 1,
      Expr::Num(n) => n.len(),
      Expr::Alg(_)
  //| Expr::Cal(_)
  //| Expr::Sq(_)
      => {
        self.iter().fold(0,
          |acc, e| acc + e.len()
        )
      }
    }
  }

  pub fn dom(&self) -> Set {
    match self {
      Expr::Cte(_) => Set::SR,
      Expr::Sym(s) => s.dom.clone(),
      Expr::Num(n) => n.dom(),
      Expr::Alg(_)
  //| Expr::Cal(_)
  //| Expr::Sq(_)
      => {
        self.iter().fold(Set::AS,
          |acc, e| acc.max(e.dom())
        )
      }
    }
  }

  pub fn free(&self, o: &Expr) -> bool {
    if self.eq(o) {
      return false;
    }

    match self {
      Expr::Cte(_)
    | Expr::Sym(_)
    | Expr::Num(_) => true,
      Expr::Alg(_)
  //| Expr::Cal(_)
  //| Expr::Sq(_)
      => {
        self.iter().fold(true,
          |acc, e| acc && e.free(o)
        )
      }
    }
  }

  pub fn subs(&self, m: &Expr, s: &Expr) -> Expr {
    if self.eq(m) {
      return s.clone();
    } else if self.free(m) {
      return self.clone();
    }

    match_term!(
      self, {
        Expr::Sym | Expr::Cte | Expr::Num => |_| s.clone(),
        Expr::Alg
    //| Expr::Cal
    //| Expr::Sq
        => |e| {
          e.subs(m, s)
        }
      }
    )
  }

  pub fn is_leaf(&self) -> bool {
    match self {
      Expr::Sym(_) | Expr::Cte(_) | Expr::Num(_) => true,
      Expr::Alg(_)
  //| Expr::Cal(_)
  //| Expr::Sq(_)
      => {
        false
      }
    }
  }

  fn ord(&self) -> u64 {
    match self {
      Expr::Sym(_) | Expr::Cte(_) => 0,

      Expr::Num(n) => n.len(),
      Expr::Alg(a) => {
        //.
        a.ord()
      }
    }
  }

  pub fn iter(
    //.
    &self,
  ) -> Iter {
    Iter {
      // root
      root: self,
    }
  }
}

impl PartialOrd for Expr {
  fn partial_cmp(&self, o: &Self) -> Option<Ordering> { Some(self.cmp(o)) }
}

impl Ord for Expr {
  fn cmp(&self, o: &Self) -> Ordering {
    match (self, o) {
      (Expr::Sym(l), Expr::Sym(r)) => l.cmp(r),
      (Expr::Num(l), Expr::Num(r)) => l.cmp(r),

      (
        Expr::Alg(Algebra::UExpr {
          //.
          map: _,
          arg: lhs,
        }),
        Expr::Alg(Algebra::UExpr {
          //.
          map: _,
          arg: rhs,
        }),
      ) => lhs.cmp(&rhs),

      (
        Expr::Alg(Algebra::BExpr {
          //.
          map: _,
          arg: (lhs_term, lhs_exp),
        }),
        Expr::Alg(Algebra::BExpr {
          //.
          map: _,
          arg: (rhs_term, rhs_exp),
        }),
      ) => lhs_term.cmp(rhs_term).then(lhs_exp.cmp(rhs_exp)),

      (
        Expr::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: _,
          arg: lhs,
        })),
        Expr::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: _,
          arg: rhs,
        })),
      ) => {
        lhs //.
          .iter()
          .rev()
          .cmp(rhs.iter().rev())
      }

      (Expr::Alg(Algebra::BExpr { map: _, arg: (term, exp) }), rhs) => term.as_ref().cmp(rhs).then(exp.as_ref().cmp(&Expr::ONE)),
      (lhs, Expr::Alg(Algebra::BExpr { map: _, arg: (term, exp) })) => lhs.cmp(term.as_ref()).then(Expr::ONE.cmp(&exp.as_ref())),

      (Expr::Alg(Algebra::AssocExpr(Assoc { map: _, arg: lhs })), rhs) => lhs.iter().rev().cmp(iter::repeat(rhs)),
      (lhs, Expr::Alg(Algebra::AssocExpr(Assoc { map: _, arg: rhs }))) => iter::repeat(lhs).cmp(rhs.iter().rev()),

      (Expr::Num(_), _) => Ordering::Less,
      (_, Expr::Num(_)) => Ordering::Greater,
      (Expr::Sym(_), _) => Ordering::Less,
      (_, Expr::Sym(_)) => Ordering::Greater,

      _ => {
        //.
        Ordering::Equal
      }
    }
  }
}

pub type Interval = ops::Range<Expr>;

pub struct Iter<'e> {
  // recursive visitor over the expressions
  root: &'e Expr,
}

impl<'e> Iter<'e> {
  pub fn fold<B, F>(
    //.
    &self,
    init: B,
    f: F,
  ) -> B
  where
    F: Fn(B, &Expr) -> B,
  {
    match self.root {
      Expr::Alg(alg) => {
        match alg {
          Algebra::UExpr {
            // 1
            map: _,
            arg,
          } => {
            //.
            f(init, arg.as_ref())
          }

          Algebra::BExpr {
            // 2
            map: _,
            arg,
          } => {
            //.
            f(f(init, arg.0.as_ref()), arg.1.as_ref())
          }

          Algebra::AssocExpr(Assoc {
            // n
            map: _,
            arg,
          }) => {
            //.
            arg.iter().fold(init, |acc, e| f(acc, e))
          }
        }
      }

      atom => {
        //.
        f(init, atom)
      }
    }
  }

  pub fn fold_rec<B, F>(
    //.
    &self,
    init: B,
    f: &F,
  ) -> B
  where
    F: Fn(B, &Expr) -> B,
  {
    let init = f(
      init, //.
      self.root,
    );

    if self.root.is_leaf() {
      init
    } else {
      self.fold(
        init,
        |acc, e| e.iter().fold_rec(acc, f), //.
      )
    }
  }

  pub fn any<F>(
    //.
    &self,
    f: &F,
  ) -> bool
  where
    F: Fn(&Expr) -> bool,
  {
    let init = f(self.root);
    if init {
      return true;
    }

    if self.root.is_leaf() {
      init
    } else {
      self.fold(
        init,
        |acc, e| acc || e.iter().any(f), //.
      )
    }
  }
}

impl fmt::Display for Expr {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match_term!(
      self, {
        Expr::Sym
      | Expr::Cte
      | Expr::Num
      | Expr::Alg
    //| Expr::Cal
    //| Expr::Sq
        => |e| {
          write!(f, "{}", e)
        }
      }
    )
  }
}
