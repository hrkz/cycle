use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul};

use crate::{Constant, Form, Integer, Number, Rational, Structure, SymbolicResult};
use crate::{Edge, Expr, Tree};

/// A list of unary operations.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum UOp {
  Id,
  Fact,
}

/// A list of binary operations.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum BOp {
  Pow,
}

/// A list of associative operations.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum AOp {
  Add,
  Mul,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Assoc {
  pub map: AOp,
  pub arg: Vec<Edge>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Algebra {
  UExpr {
    map: UOp,
    arg: Edge,
  },

  BExpr {
    map: BOp,
    arg: (Edge, Edge),
  },

  AssocExpr(
    Assoc, //.
  ),
}

impl Algebra {
  /// Apply algebraic simplifications.
  pub fn alg_trivial(&self) -> SymbolicResult<Tree> {
    match self {
      Algebra::AssocExpr(expr) => expr.trivial(),

      Algebra::UExpr {
        //.
        map: UOp::Id,
        arg,
      } => arg.trivial(),

      Algebra::UExpr {
        //.
        map: UOp::Fact,
        arg,
      } => match arg.trivial()? {
        Tree::Num(Number::Z(n)) => crate::base::algebra::factorial(n).map_or(Err(Form {}), |f| Ok(Tree::from(f))),
        expr => Ok(expr.fact()),
      },

      Algebra::BExpr {
        //.
        map: BOp::Pow,
        arg: (lhs, rhs),
      } => {
        match (lhs.trivial()?, rhs.trivial()?) {
          // ```z∞^∞ -> ~∞```
          // ```z∞^-∞ -> 0```
          // ```z∞^~∞ -> ?```
          (Tree::Cte(Constant::Infinity(_)), Tree::Cte(Constant::Infinity(Ordering::Greater))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Equal))),
          (Tree::Cte(Constant::Infinity(_)), Tree::Cte(Constant::Infinity(Ordering::Less))) => Ok(Tree::ZERO),
          (Tree::Cte(Constant::Infinity(_)), Tree::Cte(Constant::Infinity(Ordering::Equal))) => Err(Form {}),

          // ```z∞^0 = +-1^z∞ -> ?```
          (Tree::Cte(Constant::Infinity(_)), Tree::ZERO) | (Tree::ONE | Tree::NEG_ONE, Tree::Cte(Constant::Infinity(_))) => Err(Form {}),

          // ``` z∞^y, y ∈ ℚ```
          // ``` z∞^y ->   0, y < 0```
          // ```+~∞^y -> +~∞, y > 0```
          // ``` -∞^y ->   ∞, y mod 2 = 0```
          // ``` -∞^y ->  -∞, y mod 2 = 1```
          (Tree::Cte(Constant::Infinity(_)), Tree::Num(rhs)) if rhs.num().is_negative() => Ok(Tree::ZERO),
          (Tree::Cte(Constant::Infinity(z)), Tree::Num(_)) if z.is_ge() => Ok(Tree::Cte(Constant::Infinity(z))),
          (Tree::Cte(Constant::Infinity(Ordering::Less)), Tree::Num(rhs)) => Ok(Tree::Cte(Constant::Infinity(match (rhs.num() / rhs.den()).rem_euclid(2) {
            0 => Ordering::Greater,
            _ => Ordering::Less,
          }))),

          // ```x^+-∞, x ∈ ℚ```
          // ```x^+-∞ ->  0, |x|+-∞ < 0```
          // ```x^+-∞ ->  ∞, |x|+-∞ = 0, x > 0```
          // ```x^+-∞ -> ~∞, |x|+-∞ = 0, x < 0```
          (Tree::Num(lhs), Tree::Cte(Constant::Infinity(z))) if z.is_ne() => Ok(match (lhs.num().abs().cmp(&lhs.den()).cmp(&z), lhs.num().is_positive()) {
            (Ordering::Greater | Ordering::Less, _) => Tree::ZERO,
            (Ordering::Equal, true) => Tree::Cte(Constant::Infinity(Ordering::Greater)),
            (Ordering::Equal, false) => Tree::Cte(Constant::Infinity(Ordering::Equal)),
          }),

          // ```I^y, y ∈ ℤ```
          // ```I^y =  1, y mod 4 = 0```
          // ```I^y =  I, y mod 4 = 1```
          // ```I^y = -1, y mod 4 = 2```
          // ```I^y = -I, y mod 4 = 3```
          (Tree::Cte(Constant::I), Tree::Num(Number::Z(rhs))) => Ok(match rhs.rem_euclid(4) {
            0 => Tree::ONE,
            1 => Tree::Cte(Constant::I),
            2 => Tree::NEG_ONE,
            _ => Tree::Cte(Constant::I).neg(),
          }),

          // ```0^y, y ∈ ℚ```
          // ```0^y =  0, y > 0```
          // ```0^y = ~∞, y < 0```
          // ```0^0 =  ?```
          (Tree::ZERO, Tree::Num(rhs)) => match rhs.num().cmp(&0) {
            Ordering::Greater => Ok(Tree::ZERO),
            Ordering::Less => Ok(Tree::Cte(Constant::Infinity(Ordering::Equal))),
            Ordering::Equal => Err(Form {}),
          },

          // ```sqrt(-1) = (-1)^(1/2) = I```
          (Tree::NEG_ONE, Tree::Num(Number::Q(Rational { num: 1, den: 2 }))) => Ok(Tree::Cte(Constant::I)),
          // ```1^x = x^0 = 1```
          (Tree::ONE, _) | (_, Tree::ZERO) => Ok(Tree::ONE),
          // ```x^1 = x```
          (lhs, Tree::ONE) => Ok(lhs),

          // ```x ∈ ℚ, y ∈ ℤ```
          (Tree::Num(lhs), Tree::Num(Number::Z(rhs))) => Ok(Tree::Num(lhs.powi(rhs)?)),
          // ```x ∈ ℤ, y ∈ ℚ```
          (Tree::Num(Number::Z(lhs)), Tree::Num(rhs)) => Algebra::trivial_root(lhs, rhs),

          // ```(b^e)^y = b^(e*y), y ∈ ℤ```
          (Tree::Alg(Algebra::BExpr { map: BOp::Pow, arg: (b, e) }), r) if rhs.dom().le(&Structure::Z) => b.pow(e.mul(r)).trivial(),

          // ```(x_1*x_2*...*x_n)^y = x_1^y*x_2^y*...*x_n^y, y ∈ ℤ```
          (Tree::Alg(Algebra::AssocExpr(Assoc { map: AOp::Mul, arg })), Tree::Num(rhs)) if rhs.dom().le(&Structure::Z) => {
            let prod = arg.into_iter().map(|sub| sub.pow(Tree::Num(rhs.clone())).edge()).collect();
            Tree::assoc(AOp::Mul, prod).trivial()
          }

          (lhs, rhs) => {
            Ok(lhs.pow(
              rhs, //.
            ))
          }
        }
      }
    }
  }

  /// Apply root simplifications.
  pub fn trivial_root(lhs: Integer, rhs: Number) -> SymbolicResult<Tree> {
    match rhs.clone().try_root(lhs.abs()) {
      Some(Number::Z(1)) | None => Ok(Tree::from(lhs).pow(Tree::Num(rhs))),
      Some(root) => {
        let root = Tree::Num(root);
        if lhs.is_negative() {
          // ```(-x)^(p/q) = x^(p/q)*(-1)^div(p, q)*(-1)^(mod(p, q)/q)```
          let (i, r) = rhs.divrem();
          root.mul(Tree::NEG_ONE.pow(Tree::from(i)).mul(Tree::NEG_ONE.pow(Tree::from(Rational::new(r, rhs.den()))))).trivial()
        } else {
          Ok(root)
        }
      }
    }
  }

  // Helpers
  pub(crate) fn helper_prec(&self) -> u64 {
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

  fn require_parenthesis(&self, o: &Tree) -> bool {
    o.helper_len() > 1 && o.helper_prec() < self.helper_prec()
  }

  fn fmt_par(&self, o: &Tree) -> String {
    if self.require_parenthesis(o) {
      format!("({o})")
    } else {
      format!(
        // assoc
        "{o}"
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
      } => write!(f, "Id({arg})"),

      Algebra::UExpr {
        //.
        map: UOp::Fact,
        arg,
      } => write!(f, "{}!", self.fmt_par(arg)),

      Algebra::BExpr {
        //.
        map,
        arg,
      } => match map {
        BOp::Pow => write!(f, "{}^{}", self.fmt_par(&arg.0), self.fmt_par(&arg.1)),
      },

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
                  f, //.
                  " + {}",
                  self.fmt_par(e)
                )?;
              }

              AOp::Mul => {
                write!(
                  f, //.
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
  fn trivial(&self) -> SymbolicResult<Tree> {
    let mut flat = Vec::new();
    // Apply associative property.
    let Assoc { map, mut arg } = self.clone().flatten(&mut flat)?;
    // Apply commutative property.
    flat.sort_by(|lhs, rhs| self.map.cmp_poly(lhs.is_value().cmp(&rhs.is_value()), Ordering::Equal).then(rhs.cmp(lhs)));

    while !flat.is_empty() {
      let lhs_arg = flat.pop();
      let rhs_arg = flat.pop();

      match (lhs_arg, rhs_arg) {
        (None, None) => break,
        (Some(tree), None) | (None, Some(tree)) => {
          arg.push(
            tree.edge(), //.
          )
        }

        (Some(lhs), Some(rhs)) => match (map, lhs, rhs) {
          // ```z1∞ + z2∞ = ?, z1 != z2```
          (AOp::Add, Tree::Cte(Constant::Infinity(lhs)), Tree::Cte(Constant::Infinity(rhs))) if lhs != rhs => return Err(Form {}),
          // ```0*z∞ = ?```
          (AOp::Mul, Tree::ZERO, Tree::Cte(Constant::Infinity(_))) => return Err(Form {}),

          // ```0*x = 0```
          (AOp::Mul, Tree::ZERO, _) => {
            arg.resize_with(1, || Tree::edge(Tree::ZERO));
            break;
          }

          // ```x + z∞ = z∞```
          (AOp::Add, _, Tree::Cte(Constant::Infinity(z))) | (AOp::Add, Tree::Cte(Constant::Infinity(z)), _) => flat.push(Tree::Cte(Constant::Infinity(z))),
          // ```~∞*x = ~∞```
          (AOp::Mul, Tree::Cte(Constant::Infinity(Ordering::Equal)), _) | (AOp::Mul, _, Tree::Cte(Constant::Infinity(Ordering::Equal))) => flat.push(Tree::Cte(Constant::Infinity(Ordering::Equal))),

          // ```z1∞*z2∞ = sgn(z1*z2)∞```
          (AOp::Mul, Tree::Cte(Constant::Infinity(lhs)), Tree::Cte(Constant::Infinity(rhs))) => flat.push(Tree::Cte(Constant::Infinity(Constant::sign_cmp(lhs, rhs)))),

          // ```x*z∞ = sgn(x*z)∞, x ∈ ℚ```
          (AOp::Mul, Tree::Num(lhs), Tree::Cte(Constant::Infinity(z))) => flat.push(Tree::Cte(Constant::Infinity(Constant::sign_cmp(lhs.num().cmp(&0), z)))),

          // ```x, y ∈ ℚ```
          (AOp::Add, Tree::Num(lhs), Tree::Num(rhs)) => flat.push(Tree::Num(lhs.add(rhs)?)),
          (AOp::Mul, Tree::Num(lhs), Tree::Num(rhs)) => flat.push(Tree::Num(lhs.mul(rhs)?)),

          // ```x + 0 = x```
          (AOp::Add, lhs, Tree::ZERO) => flat.push(lhs),
          // ```1*x = x```
          (AOp::Mul, Tree::ONE, rhs) => flat.push(rhs),

          (_, lhs, rhs) => {
            let (lhs_base, lhs_coeff) = self.split(&lhs)?;
            let (rhs_base, rhs_coeff) = self.split(&rhs)?;

            let factor = if lhs_base == rhs_base {
              // ```c*x + d*x = (c + d)*x, {c, d} ∈ ℚ``` or
              // ```x^c * x^d = x^(c + d)```
              let coeff = lhs_coeff.add(rhs_coeff).trivial()?;
              self.merge(lhs_base, coeff)?
            } else {
              arg.push(lhs.edge());
              rhs
            };

            if factor != map.id() {
              flat.push(
                factor, //.
              )
            }
          }
        },
      }
    }

    Assoc {
      map, //.
      arg,
    }
    .arity()
  }

  fn flatten(mut self, flat: &mut Vec<Tree>) -> SymbolicResult<Assoc> {
    flat.reserve(self.arg.len());
    while let Some(expr) = self.arg.pop() {
      match expr.trivial()? {
        Tree::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: smap,
          arg: sarg,
        }))
          if self.map == smap =>
        {
          sarg.iter().for_each(|sub| self.arg.push(sub.clone()))
        }

        expr => {
          flat.push(
            expr, //.
          )
        }
      }
    }

    Ok(self)
  }

  fn arity(mut self) -> SymbolicResult<Tree> {
    Ok(match self.arg.len() {
      0 => self.map.id(),
      1 => self.arg.remove(0).trivial()?,

      _ => Tree::assoc(
        self.map, //.
        self.arg,
      ),
    })
  }

  /// Split an associative operation.
  /// [`split`](x) = (b, c)
  /// [`split`](x) = [`split`]([`merge`](b, c)) = (b, c)
  fn split(&self, expr: &Tree) -> SymbolicResult<(Tree, Tree)> {
    match (self.map, &expr) {
      (
        AOp::Add,
        Tree::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: AOp::Mul,
          arg,
        })),
      ) => {
        if let Some((c, b)) = arg.split_first() {
          return Ok((
            Tree::assoc(AOp::Mul, b.to_vec()).trivial()?,
            Tree::from(c), // ```c*b```
          ));
        }
      }
      (AOp::Mul, Tree::Alg(Algebra::BExpr { map: BOp::Pow, arg: (b, c) })) => {
        return Ok((
          Tree::from(b),
          Tree::from(c), // ```b^c```
        ));
      }

      _ => {
        //.
      }
    }

    Ok((
      expr.clone(), // ```b```
      Tree::ONE,
    ))
  }

  /// Merge an associative base and coefficient.
  /// [`merge`](b, c) = x
  /// [`merge`](b, c) = [`merge`]([`split`](x)) = x
  fn merge(&self, base: Tree, coeff: Tree) -> SymbolicResult<Tree> {
    if coeff != Tree::ONE {
      match self.map {
        // ```c*b```
        AOp::Add => coeff.mul(base),
        // ```b^c```
        AOp::Mul => base.pow(coeff),
      }
      .trivial()
    } else {
      // ```1*b = b``` or
      // ```b^1 = b```
      Ok(base)
    }
  }
}

impl AOp {
  /// Return the associative identity element.
  /// (S, ∘), ∃e, e ∘ a = a ∘ e = a ∀a ∈ S
  /// [Semigroup](https://en.wikipedia.org/wiki/Semigroup)
  const fn id(&self) -> Tree {
    match self {
      // ```Id(+) = 0```
      AOp::Add => Tree::ZERO,
      // ```Id(*) = 1```
      AOp::Mul => Tree::ONE,
    }
  }

  pub const fn cmp_poly(&self, ord: Ordering, poly_cmp: Ordering) -> Ordering {
    match self {
      // ```x + c```
      AOp::Add => poly_cmp.then(ord.reverse()),
      // ```c*x```
      AOp::Mul => ord,
    }
  }
}

impl Tree {
  pub(crate) fn assoc(
    //.
    map: AOp,
    arg: Vec<Edge>,
  ) -> Tree {
    Tree::Alg(Algebra::AssocExpr(Assoc {
      //.
      map,
      arg,
    }))
  }
}
