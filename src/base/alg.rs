use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::{Expr, Number, Set};

#[derive(Debug, Clone, Hash, PartialEq, Copy)]
pub enum UOp {
  Elem,
  Fact,
}

#[derive(Debug, Clone, Hash, PartialEq, Copy)]
pub enum BOp {
  Pow,
}

#[derive(Debug, Clone, Hash, PartialEq, Copy)]
pub enum AOp {
  Add,
  Mul,
}

#[derive(Debug, Clone, Hash, PartialEq)]
pub struct Assoc {
  pub map: AOp,
  pub arg: Vec<Expr>,
}

#[derive(Debug, Clone, Hash, PartialEq)]
pub enum Algebra {
  UExpr {
    map: UOp,
    arg: Box<Expr>,
  },

  BExpr {
    map: BOp,
    arg: (Box<Expr>, Box<Expr>),
  },

  AssocExpr(
    //.
    Assoc,
  ),
}

impl Algebra {
  pub fn ord(&self) -> u64 {
    match self {
      Algebra::UExpr {
        //.
        map,
        arg: _,
      } => {
        match map {
          //.
          UOp::Elem => 2,
          UOp::Fact => 4,
        }
      }

      Algebra::BExpr {
        //.
        map,
        arg: _,
      } => {
        match map {
          //.
          BOp::Pow => 3,
        }
      }

      Algebra::AssocExpr(Assoc {
        //.
        map,
        arg: _,
      }) => {
        match map {
          //.
          AOp::Add => 1,
          AOp::Mul => 2,
        }
      }
    }
  }

  pub fn len(&self) -> u64 {
    match self {
      Algebra::UExpr { map: _, arg } => arg.len(),
      Algebra::BExpr { map: _, arg } => arg.0.len() + arg.1.len(),

      Algebra::AssocExpr(Assoc {
        //.
        map: _,
        arg,
      }) => {
        arg
          .iter()
          .map(
            |e| e.len(), //.
          )
          .sum()
      }
    }
  }

  pub fn dom(&self) -> Set {
    match self {
      Algebra::UExpr { map: _, arg } => arg.dom(),
      Algebra::BExpr { map: _, arg } => std::cmp::max(arg.0.dom(), arg.1.dom()),

      Algebra::AssocExpr(Assoc {
        //.
        map: _,
        arg,
      }) => {
        arg.iter().map(|e| e.dom()).max().unwrap_or(
          Set::SR, // symbolic
        )
      }
    }
  }

  pub fn free(&self, o: &Expr) -> bool {
    match self {
      Algebra::UExpr { map: _, arg } => arg.free(o),
      Algebra::BExpr { map: _, arg } => arg.0.free(o) && arg.1.free(o),

      Algebra::AssocExpr(Assoc {
        //.
        map: _,
        arg,
      }) => {
        arg.iter().all(
          |e| e.free(o), //.
        )
      }
    }
  }

  pub fn subs(&self, m: &Expr, s: &Expr) -> Expr {
    match self {
      Algebra::UExpr {
        //.
        map,
        arg,
      } => Expr::Alg(Algebra::UExpr {
        map: *map,
        arg: Box::new(arg.subs(m, s)),
      }),

      Algebra::BExpr {
        //.
        map,
        arg,
      } => Expr::Alg(Algebra::BExpr {
        map: *map,
        arg: (Box::new(arg.0.subs(m, s)), Box::new(arg.1.subs(m, s))),
      }),

      Algebra::AssocExpr(Assoc {
        //.
        map,
        arg,
      }) => Expr::Alg(Algebra::AssocExpr(Assoc {
        map: *map,
        arg: arg.iter().map(|x| x.subs(m, s)).collect(),
      })),
    }
  }

  fn require_parenthesis(&self, o: &Expr) -> bool { o.len() > 1 && o.ord() < self.ord() }

  fn fmt_par(&self, o: &Expr) -> String {
    if self.require_parenthesis(o) {
      format!("({})", o)
    } else {
      format!(
        // assoc
        "{}", 
        o
        )
    }
  }
}

impl fmt::Display for Algebra {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Algebra::UExpr {
        //.
        map,
        arg,
      } => match map {
        UOp::Elem => write!(f, "elem"),
        UOp::Fact => write!(f, "{}!", self.fmt_par(arg)),
      },

      Algebra::BExpr {
        //.
        map,
        arg,
      } => {
        //.
        match map {
          BOp::Pow => write!(f, "{}^{}", self.fmt_par(&arg.0), self.fmt_par(&arg.1)),
        }
      }

      Algebra::AssocExpr(Assoc {
        //.
        map,
        arg,
      }) => {
        let mut iter = arg.iter();

        if let Some(e) = iter.next() {
          write!(f, "{}", self.fmt_par(e))?;

          for e in iter {
            match map {
              AOp::Add => {
                write!(
                  //.
                  f,
                  " + {}",
                  self.fmt_par(e)
                )?;
              }

              AOp::Mul => {
                write!(
                  //.
                  f,
                  "*{}",
                  self.fmt_par(e)
                )?;
              }
            }
          }
        }

        Ok(())
      }
    }
  }
}

impl Expr {
  /// ```a!```
  pub fn r#fact(self) -> Self { Self::Alg(Algebra::UExpr { map: UOp::Fact, arg: Box::new(self) }) }

  /// ```a^b```
  pub fn r#pow(
    //.
    self,
    o: Self,
  ) -> Self {
    Self::Alg(Algebra::BExpr {
      map: BOp::Pow,
      arg: (Box::new(self), Box::new(o)),
    })
  }
}

impl Add for Expr {
  type Output = Self;
  /// ```a + b```
  fn add(self, o: Self) -> Self { Self::Alg(Algebra::AssocExpr(Assoc { map: AOp::Add, arg: vec![self, o] })) }
}

impl Mul for Expr {
  type Output = Self;
  /// ```a*b```
  fn mul(self, o: Self) -> Self { Self::Alg(Algebra::AssocExpr(Assoc { map: AOp::Mul, arg: vec![self, o] })) }
}

impl Neg for Expr {
  type Output = Self;
  /// ```-a = (-1)*a```
  fn neg(self) -> Self { Self::Num(Number::NEG_ONE).mul(self) }
}

impl Sub for Expr {
  type Output = Self;
  /// ```a - b = a + (-b)```
  fn sub(self, o: Self) -> Self { self.add(o.neg()) }
}

impl Div for Expr {
  type Output = Self;
  /// ```a/b = a * b^-1```
  fn div(self, o: Self) -> Self { self.mul(o.pow(Self::Num(Number::NEG_ONE))) }
}
