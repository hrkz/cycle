use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::{Expr, Form, Number, Set, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum UOp {
  Fact,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum BOp {
  Pow,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum AOp {
  Add,
  Mul,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Assoc {
  pub map: AOp,
  pub arg: Vec<Expr>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
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
  pub fn trivial(self) -> SymbolicResult<Expr> {
    match self {
      Algebra::UExpr {
        //.
        map: _,
        arg: _,
      } => Ok(Expr::Alg(self)),

      Algebra::BExpr {
        //.
        map: BOp::Pow,
        arg: (lhs, rhs),
      } => {
        match (lhs.trivial()?, rhs.trivial()?) {
          // ```x ∈ ℚ, y ∈ ℤ```
          (Expr::Num(lhs), Expr::Num(Number::Z(rhs))) => Ok(Expr::Num(lhs.pow(rhs)?)),

          // ```1^x = x^0 = 1```
          (Expr::ONE, _) | (_, Expr::ZERO) => Ok(Expr::ONE),

          // ```x^1 = x```
          (lhs, Expr::ONE) => Ok(lhs),

          // ```0^y = 0, y ∈ ℚ > 0```
          (Expr::ZERO, Expr::Num(rhs)) => {
            if rhs
              //.
              .num()
              .is_negative()
            {
              Err(Form {})
            } else {
              Ok(Expr::ZERO)
            }
          }

          // ```(b^e)^p = b^(e*p), p ∈ ℤ```
          (Expr::Alg(Algebra::BExpr { map: BOp::Pow, arg: (b, e) }), p) if p.dom().le(&Set::Z) => b.pow(e.mul(p).trivial()?).trivial(),

          // ```(x_1 * x_2 * ... * x_n)^p = x_1^p * x_2^p * ... * x_n^p, p ∈ ℤ```
          (Expr::Alg(Algebra::AssocExpr(Assoc { map: AOp::Mul, arg })), Expr::Num(p)) if p.dom().le(&Set::Z) => {
            let prod = arg.into_iter().map(|sub| sub.pow(Expr::Num(p.clone()))).collect();
            Expr::assoc(AOp::Mul, prod).trivial()
          }

          (lhs, rhs) => {
            //.
            Ok(lhs.pow(rhs))
          }
        }
      }

      Algebra::AssocExpr(expr) => {
        Ok(
          expr //.
            .assoc()?
            .trivial()?
            .id(),
        )
      }
    }
  }

  pub fn ord(&self) -> u64 {
    match self {
      Algebra::UExpr {
        //.
        map,
        arg: _,
      } => {
        match map {
          //.
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

impl Assoc {
  fn assoc(mut self) -> SymbolicResult<Assoc> {
    let mut arg = Vec::new();

    while let Some(expr) = self.arg.pop() {
      match expr.trivial()? {
        Expr::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: sub_map,
          arg: sub_arg,
        }))
          if self.map == sub_map =>
        {
          sub_arg.into_iter().for_each(|x| self.arg.push(x))
        }

        a => {
          //.
          arg.push(a)
        }
      }
    }

    Ok(Assoc {
      //.
      map: self.map,
      arg,
    })
  }

  fn trivial(mut self) -> SymbolicResult<Assoc> {
    let mut arg = Vec::new();

    self.arg.sort_by(|lhs, rhs| lhs.cmp(rhs).reverse());
    while !self.arg.is_empty() {
      let lhs_arg = self.arg.pop();
      let rhs_arg = self.arg.pop();

      match (lhs_arg, rhs_arg) {
        (None, None) => break,
        (Some(expr), None) | (None, Some(expr)) => {
          arg.push(expr) //.
        }

        (Some(lhs), Some(rhs)) => match (self.map, lhs, rhs) {
          // ```0*x = 0```
          (AOp::Mul, Expr::ZERO, _) => {
            arg.resize_with(1, || Expr::ZERO);
            break;
          }

          // ```x, y ∈ ℚ```
          (AOp::Add, Expr::Num(lhs), Expr::Num(rhs)) => self.arg.push(Expr::Num(lhs.add(rhs)?)),
          (AOp::Mul, Expr::Num(lhs), Expr::Num(rhs)) => self.arg.push(Expr::Num(lhs.mul(rhs)?)),

          // ```0 + x = x```
          (AOp::Add, Expr::ZERO, o) => self.arg.push(o),
          // ```1*x = x```
          (AOp::Mul, Expr::ONE, o) => self.arg.push(o),

          // ```c*(x_1 + x_2 + ... + x_n) = c*x_1 + c*x_2 + ... + c*x_n, c ∈ ℚ```
          (AOp::Mul, Expr::Num(c), Expr::Alg(Algebra::AssocExpr(Assoc { map: AOp::Add, arg }))) if c.dom().le(&Set::Q) => {
            let sum = arg.into_iter().map(|sub| sub.mul(Expr::Num(c.clone()))).collect();
            self.arg.push(Expr::assoc(AOp::Add, sum).trivial()?)
          }

          (map, lhs, rhs) => {
            let (lhs_base, lhs_coeff) = self.distrib(&lhs)?;
            let (rhs_base, rhs_coeff) = self.distrib(&rhs)?;

            if lhs_base == rhs_base {
              let coeff = lhs_coeff.add(rhs_coeff).trivial()?;
              let factor = match map {
                // ```c*x + d*x = (c + d)*x```
                AOp::Add => rhs_base.mul(coeff).trivial()?,
                // ```x^c * x^d = x^(c + d)```
                AOp::Mul => rhs_base.pow(coeff).trivial()?,
              };

              self.arg.push(
                factor, //.
              )
            } else {
              arg.push(lhs);
              self.arg.push(rhs)
            }
          }
        },
      }
    }

    Ok(Assoc {
      //.
      map: self.map,
      arg,
    })
  }

  fn id(mut self) -> Expr {
    match (
      self.map, //.
      self.arg.len(),
    ) {
      // ```Id(+) = 0```
      (AOp::Add, 0) => Expr::ZERO,
      // ```Id(*) = 1```
      (AOp::Mul, 0) => Expr::ONE,

      (_, 1) => self.arg.swap_remove(0),

      _ => {
        Expr::assoc(
          self.map, //.
          self.arg,
        )
      }
    }
  }

  fn distrib(&self, expr: &Expr) -> SymbolicResult<(Expr, Expr)> {
    match (
      self.map, //.
      expr,
    ) {
      (
        AOp::Add,
        Expr::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: AOp::Mul,
          arg,
        })),
      ) => {
        // ```c*t```
        if let Some((c @ Expr::Num(_), t)) = arg.split_first() {
          return Ok((Expr::assoc(AOp::Mul, t.to_vec()).trivial()?, c.clone()));
        }
      }

      (
        AOp::Mul,
        Expr::Alg(Algebra::BExpr {
          //.
          map: BOp::Pow,
          arg: (b, e),
        }),
      ) => {
        return Ok((
          *b.clone(), // ```b^e```
          *e.clone(),
        ));
      }

      _ => {
        //.
        ()
      }
    }

    Ok((
      expr.clone(), // ```x```
      Expr::ONE,
    ))
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

  pub fn r#assoc(map: AOp, arg: Vec<Expr>) -> Self {
    Self::Alg(Algebra::AssocExpr(Assoc {
      //.
      map,
      arg,
    }))
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
  fn neg(self) -> Self { Self::NEG_ONE.mul(self) }
}

impl Sub for Expr {
  type Output = Self;
  /// ```a - b = a + (-b)```
  fn sub(self, o: Self) -> Self { self.add(o.neg()) }
}

impl Div for Expr {
  type Output = Self;
  /// ```a/b = a * b^-1```
  fn div(self, o: Self) -> Self { self.mul(o.pow(Self::NEG_ONE)) }
}
