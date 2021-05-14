use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::{Constant, Expr, Form, Number, Rational, Set, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum UOp {
  Id,
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
      Algebra::AssocExpr(expr) => Ok(expr.flatten()?.trivial()?.arity()),

      Algebra::UExpr {
        //.
        map: UOp::Id,
        arg,
      } => arg.trivial(),

      Algebra::BExpr {
        //.
        map: BOp::Pow,
        arg: (lhs, rhs),
      } => {
        match (lhs.trivial()?, rhs.trivial()?) {
          // ```_∞^∞ = ~∞```
          // ```_∞^-∞ = 0```
          // ```_∞^~∞ = ?```
          (Expr::Cte(Constant::Infinity(_)), Expr::Cte(Constant::Infinity(1))) => Ok(Expr::Cte(Constant::Infinity(0))),
          (Expr::Cte(Constant::Infinity(_)), Expr::Cte(Constant::Infinity(-1))) => Ok(Expr::ZERO),
          (Expr::Cte(Constant::Infinity(_)), Expr::Cte(Constant::Infinity(0))) => Err(Form {}),

          // ```_∞^0 = 1^_∞ = ?```
          (Expr::Cte(Constant::Infinity(_)), Expr::ZERO) | (Expr::ONE, Expr::Cte(Constant::Infinity(_))) => Err(Form {}),

          // ```_∞^y, y ∈ ℚ```
          (Expr::Cte(Constant::Infinity(z)), Expr::Num(rhs)) => {
            // ```_∞^y -> 0, y < 0```
            // ```+∞^y ->  ∞, y > 0```
            // ```-∞^y ->  ∞, y mod 2 = 0```
            // ```-∞^y -> -∞, y mod 2 = 1```
            let n = rhs.num();
            Ok((n < 0).then(|| Expr::ZERO).unwrap_or(Expr::Cte(Constant::Infinity(z.pow(n.div(rhs.den()).rem_euclid(2) as u32)))))
          }

          // ```x^_∞, x ∈ ℚ```
          (Expr::Num(lhs), Expr::Cte(Constant::Infinity(z))) => {
            // ```x^_∞ -> 0, |x|_∞ < 0```
            // ```x^+∞ ->  ∞, |x|+∞ > 0, x > 0```
            // ```x^+∞ -> ~∞, |x|+∞ > 0, x < 0```
            // ```x^-∞ ->  ∞, |x|-∞ < 0, x > 0```
            // ```x^-∞ -> ~∞, |x|-∞ < 0, x < 0```
            let n = (lhs.num().abs() - lhs.den()) * z;
            Ok((n < 0).then(|| Expr::ZERO).unwrap_or(Expr::Cte(Constant::Infinity(i128::from(lhs.num() > 0)))))
          }

          // ```I^y, y ∈ ℤ```
          (Expr::Cte(Constant::I), Expr::Num(Number::Z(rhs))) => {
            Ok(match rhs.rem_euclid(4) {
              // ```I^y =  1, y mod 4 = 0```
              // ```I^y =  I, y mod 4 = 1```
              // ```I^y = -1, y mod 4 = 2```
              // ```I^y = -I, y mod 4 = 3```
              0 => Expr::ONE,
              1 => Expr::Cte(Constant::I),
              2 => Expr::NEG_ONE,
              _ => Expr::Cte(Constant::I).neg(),
            })
          }

          // ```0^0 = ?```
          (Expr::ZERO, Expr::ZERO) => Err(Form {}),
          // ```0^y = 0, y ∈ ℚ > 0```
          (Expr::ZERO, Expr::Num(rhs)) => {
            if rhs //.
              .num()
              .is_negative()
            {
              Ok(Expr::Cte(Constant::Infinity(0)))
            } else {
              Ok(Expr::ZERO)
            }
          }

          // ```sqrt(-1) = (-1)^(1/2) = I```
          //(Expr::NEG_ONE, Expr::HALF) => Ok(Expr::Cte(Constant::I)),

          // ```1^x = x^0 = 1```
          (Expr::ONE, _) | (_, Expr::ZERO) => Ok(Expr::ONE),
          // ```x^1 = x```
          (lhs, Expr::ONE) => Ok(lhs),

          // ```x ∈ ℚ, y ∈ ℤ```
          (Expr::Num(lhs), Expr::Num(Number::Z(rhs))) => Ok(Expr::Num(lhs.powi(rhs)?)),
          // ```x ∈ ℤ, y ∈ ℚ```
          (Expr::Num(Number::Z(lhs)), Expr::Num(rhs)) => match rhs.clone().try_root(lhs.abs()) {
            Some(Number::Z(1)) | None => Ok(Expr::from(lhs).pow(Expr::Num(rhs))),
            Some(root) => {
              let root = Expr::Num(root);

              if lhs.is_negative() {
                // ```(-x)^y = x^y*(-1)^y```
                let (
                  //.
                  i,
                  r,
                ) = rhs.divmod();
                if i != 0 {
                  // ```(-x)^(p/q) = x^(p/q)*(-1)^div(p, q)*(-1)^(mod(p, q)/q)```
                  (root * Expr::NEG_ONE.pow(Expr::from(i)) * Expr::NEG_ONE.pow(Expr::Num(Number::Q(Rational::new(r, rhs.den()))))).trivial()
                } else {
                  // ```(-x)^(p/q) = x^(p/q)*(-1)^(p/q)```
                  (root * Expr::NEG_ONE.pow(Expr::Num(rhs))).trivial()
                }
              } else {
                Ok(root)
              }
            }
          },

          // ```(b^e)^y = b^(e*y), y ∈ ℤ```
          (Expr::Alg(Algebra::BExpr { map: BOp::Pow, arg: (b, e) }), rhs) if rhs.dom().le(&Set::Z) => b.pow(e.mul(rhs)).trivial(),

          // ```(x_1*x_2*...*x_n)^y = x_1^y*x_2^y*...*x_n^y, y ∈ ℤ```
          (Expr::Alg(Algebra::AssocExpr(Assoc { map: AOp::Mul, arg })), Expr::Num(rhs)) if rhs.dom().le(&Set::Z) => {
            let prod = arg.into_iter().map(|sub| sub.pow(Expr::Num(rhs.clone()))).collect();
            Expr::assoc(AOp::Mul, prod).trivial()
          }

          (lhs, rhs) => {
            Ok(lhs.pow(rhs)) //.
          }
        }
      }
    }
  }

  pub fn ord(&self) -> u64 {
    match self {
      Algebra::UExpr {
        //.
        map: _,
        arg: _,
      } => {
        //.
        4
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
        map: UOp::Id,
        arg,
      } => write!(f, "Id({})", arg),

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
  fn flatten(mut self) -> SymbolicResult<Assoc> {
    let mut arg = Vec::new();

    while let Some(expr) = self.arg.pop() {
      match expr.trivial()? {
        Expr::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: smap,
          arg: sarg,
        }))
          if self.map == smap =>
        {
          sarg.into_iter().for_each(|x| self.arg.push(x))
        }

        a => {
          arg.push(a) //.
        }
      }
    }

    Ok(Assoc {
      //.
      map: self.map,
      arg,
    })
  }

  fn arity(mut self) -> Expr {
    match self.arg.len() {
      0 => self.id(),
      1 => self.arg.swap_remove(0),

      _ => {
        Expr::assoc(
          self.map, //.
          self.arg,
        )
      }
    }
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
          (AOp::Add, Expr::Cte(Constant::Infinity(lhs)), Expr::Cte(Constant::Infinity(rhs))) if lhs != rhs => return Err(Form {}),
          // ```0*_∞ = ?```
          (AOp::Mul, Expr::ZERO, Expr::Cte(Constant::Infinity(_))) => return Err(Form {}),

          // ```0*x = 0```
          (AOp::Mul, Expr::ZERO, _) => {
            arg.resize_with(1, || Expr::ZERO);
            break;
          }

          // ```x + _∞ = _∞```
          (AOp::Add, _, Expr::Cte(Constant::Infinity(z))) | (AOp::Add, Expr::Cte(Constant::Infinity(z)), _) => self.arg.push(Expr::Cte(Constant::Infinity(z))),

          // ```_x ∞*_y ∞ = sgn(_x*_y)∞```
          (AOp::Mul, Expr::Cte(Constant::Infinity(lhs)), Expr::Cte(Constant::Infinity(rhs))) => self.arg.push(Expr::Cte(Constant::Infinity(lhs.mul(rhs)))),
          // ```x*_∞ = sgn(x*_)∞, x ∈ ℚ```
          (AOp::Mul, Expr::Num(lhs), Expr::Cte(Constant::Infinity(z))) => self.arg.push(Expr::Cte(Constant::Infinity(lhs.num().mul(z).signum()))),

          // ```x, y ∈ ℚ```
          (AOp::Add, Expr::Num(lhs), Expr::Num(rhs)) => self.arg.push(Expr::Num(lhs.add(rhs)?)),
          (AOp::Mul, Expr::Num(lhs), Expr::Num(rhs)) => self.arg.push(Expr::Num(lhs.mul(rhs)?)),

          // ```0 + x = x```
          (AOp::Add, Expr::ZERO, rhs) => self.arg.push(rhs),
          // ```1*x = x```
          (AOp::Mul, Expr::ONE, rhs) => self.arg.push(rhs),

          // ```x*(y_1 + y_2 + ... + y_n) = x*y_1 + x*y_2 + ... + x*y_n, x ∈ ℚ```
          (AOp::Mul, Expr::Num(lhs), Expr::Alg(Algebra::AssocExpr(Assoc { map: AOp::Add, arg }))) if lhs.dom().le(&Set::Q) => {
            let sum = arg.into_iter().map(|sub| sub.mul(Expr::Num(lhs.clone()))).collect();
            self.arg.push(Expr::assoc(AOp::Add, sum).trivial()?)
          }

          (_, lhs, rhs) => {
            let (lhs_base, lhs_coeff) = self.split(lhs)?;
            let (rhs_base, rhs_coeff) = self.split(rhs)?;

            let factor = if lhs_base == rhs_base {
              // ```c*x + d*x = (c + d)*x, {c, d} ∈ ℚ``` or
              // ```x^c * x^d = x^(c + d)```
              let coeff = lhs_coeff.add(rhs_coeff).trivial()?;
              self.merge(lhs_base, coeff).trivial()?
            } else {
              arg.push(self.merge(
                lhs_base, //.
                lhs_coeff,
              ));
              self.merge(
                rhs_base, //.
                rhs_coeff,
              )
            };

            if factor != self.id() {
              self.arg.push(
                factor, //.
              )
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

  fn split(&self, expr: Expr) -> SymbolicResult<(Expr, Expr)> {
    // Splitting
    // [`split`](x) = (b, c)
    // [`split`](x) = [`split`]([`merge`](b, c)) = (b, c)
    match (
      //.
      self.map, &expr,
    ) {
      (
        AOp::Add,
        Expr::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: AOp::Mul,
          arg,
        })),
      ) => {
        if let Some((c @ Expr::Num(_), b)) = arg.split_first() {
          return Ok((
            Expr::assoc(AOp::Mul, b.to_vec()).trivial()?, // ```c*b```
            c.clone(),
          ));
        }
      }

      (
        AOp::Mul,
        Expr::Alg(Algebra::BExpr {
          //.
          map: BOp::Pow,
          arg: (b, c),
        }),
      ) => {
        return Ok((
          *b.clone(), // ```b^c```
          *c.clone(),
        ));
      }

      _ => {
        //.
        ()
      }
    }

    Ok((
      expr, // ```b```
      Expr::ONE,
    ))
  }

  fn merge(&self, base: Expr, coeff: Expr) -> Expr {
    // Merging
    // [`merge`](b, c) = x
    // [`merge`](b, c) = [`merge`]([`split`](x)) = x
    if coeff != Expr::ONE {
      match self.map {
        // ```c*b```
        AOp::Add => coeff.mul(base),
        // ```b^c```
        AOp::Mul => base.pow(coeff),
      }
    } else {
      // ```1*b = b``` or
      // ```b^1 = b```
      base
    }
  }

  const fn id(&self) -> Expr {
    // Identity element
    // (S, ∘), ∃e, e ∘ a = a ∘ e = a ∀a ∈ S
    // [Semigroup](https://en.wikipedia.org/wiki/Semigroup)
    match self.map {
      // ```Id(+) = 0```
      AOp::Add => Expr::ZERO,
      // ```Id(*) = 1```
      AOp::Mul => Expr::ONE,
    }
  }
}

impl Expr {
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

  /// ```b√a```
  pub fn r#root(self, o: Self) -> Self { self.pow(Expr::ONE / o) }

  /// ```√a```
  pub fn r#sqrt(self) -> Self { self.pow(Expr::HALF) }

  pub(crate) fn r#assoc(
    //.
    map: AOp,
    arg: Vec<Expr>,
  ) -> Self {
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
