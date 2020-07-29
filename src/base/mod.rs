pub mod alg;
pub mod ring;

use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

use alg::Algebra;
use ring::{Constant, Number, Ring, SymbolicResult};

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct Symbol {
  name: String,
  ring: Ring,
}

impl Symbol {
  pub fn new(name_str: &str, ring: Ring) -> Rc<Symbol> {
    let name = name_str.replace(&[' ', '+', '-', '*', '/', '^', '=', '(', ')', '{', '}', '#', '~'][..], "");
    // any non-whitespace, non-special character
    assert_eq!(name, name_str);

    Rc::new(Symbol {
      // extension to other formattings
      name,
      ring,
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

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
  /// Symbol (variable) on a ring
  Sym(Rc<Symbol>),
  /// Special constant
  Cte(Rc<Constant>),

  /// Exact number
  Num(Number),

  /// Algebraic operation
  Alg(Algebra),
  //Der(Derivative),
  //Int(Integral),
  //Seq(Sequence),
}

impl Expr {
  pub fn trivial(self) -> SymbolicResult<Expr> { Ok(self) }

  pub fn ord(&self) -> u64 {
    match_term!(
      self, {
        Expr::Sym | Expr::Cte => |_| 0,
        Expr::Num
      | Expr::Alg
      //| Expr::Der
      //| Expr::Int
      //| Expr::Seq
        => |e| {
          e.ord()
        }
      }
    )
  }

  pub fn len(&self) -> u64 {
    match_term!(
      self, {
        Expr::Sym | Expr::Cte => |_| 1,
        Expr::Num
      | Expr::Alg
      //| Expr::Der
      //| Expr::Int
      //| Expr::Seq
        => |e| {
          e.len()
        }
      }
    )
  }

  pub fn free(&self, o: &Expr) -> bool {
    if self == o {
      false
    } else {
      match_term!(
        self, {
          Expr::Sym
        | Expr::Cte
        | Expr::Num => |_| true,
          Expr::Alg
          //| Expr::Der
          //| Expr::Int
          //| Expr::Seq
          => |e| {
            e.free(o)
          }
        }
      )
    }
  }

  pub fn subs(&self, m: &Expr, s: &Expr) -> Expr {
    if self.free(m) {
      return self.clone();
    }

    match_term!(
      self, {
        Expr::Sym
      | Expr::Cte
      | Expr::Num => |_| s.clone(),
        Expr::Alg
      //| Expr::Der
      //| Expr::Int
      //| Expr::Seq
        => |e| {
          e.subs(m, s)
        }
      }
    )
  }

  pub fn iter(
    //.
    &self,
  ) -> impl Iterator<Item = &Expr> + '_ {
    Iter {
      // root
      stack: vec![self],
    }
  }
}

impl Eq for Expr {}
impl PartialOrd for Expr {
  fn partial_cmp(&self, o: &Self) -> Option<Ordering> { Some(self.cmp(o)) }
}

impl Ord for Expr {
  fn cmp(&self, o: &Self) -> Ordering {
    match (self, o) {
      (Expr::Sym(l), Expr::Sym(r)) => l.cmp(r),
      (Expr::Num(l), Expr::Num(r)) => r.cmp(l),

      (Expr::Sym(_), _) => Ordering::Less,
      (_, Expr::Sym(_)) => Ordering::Greater,
      (Expr::Num(_), _) => Ordering::Less,
      (_, Expr::Num(_)) => Ordering::Greater,

      _ => {
        //.
        Ordering::Equal
      }
    }
  }
}

struct Iter<'e> {
  // recursive depth-first visitor over the expressions
  stack: Vec<&'e Expr>,
}

impl<'e> Iterator for Iter<'e> {
  type Item = &'e Expr;

  fn next(&mut self) -> Option<Self::Item> {
    let curr = self.stack.pop()?;

    match curr {
      Expr::Alg(alg) => {
        match alg {
          Algebra::UExpr {
            // 1
            map: _,
            arg,
          } => {
            //.
            self.stack.push(&arg)
          }

          Algebra::BExpr {
            // 2
            map: _,
            arg,
          } => {
            self.stack.push(&arg.0);
            self.stack.push(&arg.1);
          }

          Algebra::FieldExpr(alg::Field {
            // n
            map: _,
            arg,
          }) => {
            arg.iter().for_each(
              //.
              |e| self.stack.push(&e),
            )
          }
        }
      }

      _ => (),
    }

    Some(curr)
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
      //| Expr::Der
      //| Expr::Int
      //| Expr::Seq
        => |e| {
          write!(f, "{}", e)
        }
      }
    )
  }
}
