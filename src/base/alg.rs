use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul};

use crate::{Constant, Form, Integer, Natural, Number, Rational, SymbolicResult};
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
  #[inline]
  pub fn alg_trivial(self) -> SymbolicResult<Tree> {
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
        Tree::Num(Number::Int(z)) => Natural::try_from(z).map(|n| Tree::from(Integer::from(Natural::factorial(n)))).map_err(|_| Form {}),
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
          (Tree::Cte(Constant::Infinity(_)), Tree::Cte(Constant::Infinity(Ordering::Less))) => Ok(Tree::from(0)),
          (Tree::Cte(Constant::Infinity(_)), Tree::Cte(Constant::Infinity(Ordering::Equal))) => Err(Form {}),

          // ```z∞^0 = +-1^z∞ -> ?```
          (Tree::Cte(Constant::Infinity(_)), Tree::ZERO) | (Tree::ONE | Tree::NEG_ONE, Tree::Cte(Constant::Infinity(_))) => Err(Form {}),

          // ``` z∞^y, y ∈ ℚ```
          // ``` z∞^y ->   0, y < 0```
          // ```+~∞^y -> +~∞, y > 0```
          // ``` -∞^y ->   ∞, y mod 2 = 0```
          // ``` -∞^y ->  -∞, y mod 2 = 1```
          (Tree::Cte(Constant::Infinity(_)), Tree::Num(rhs)) if rhs.num().is_negative() => Ok(Tree::from(0)),
          (Tree::Cte(Constant::Infinity(z)), Tree::Num(_)) if z.is_ge() => Ok(Tree::Cte(Constant::Infinity(z))),
          (Tree::Cte(Constant::Infinity(Ordering::Less)), Tree::Num(rhs)) => Ok(Tree::Cte(Constant::Infinity(match (rhs.num().clone() / rhs.den()).rem_euclid(Integer::from(2)) {
            Integer::ZERO => Ordering::Greater,
            _ => Ordering::Less,
          }))),

          // ```x^+-∞, x ∈ ℚ```
          // ```x^+-∞ ->  0, |x|+-∞ < 0```
          // ```x^+-∞ ->  ∞, |x|+-∞ = 0, x > 0```
          // ```x^+-∞ -> ~∞, |x|+-∞ = 0, x < 0```
          (Tree::Num(lhs), Tree::Cte(Constant::Infinity(z))) if z.is_ne() => Ok(match (Integer::from(lhs.num().clone().abs()).cmp(&lhs.den()).cmp(&z), lhs.num().is_positive()) {
            (Ordering::Greater | Ordering::Less, _) => Tree::from(0),
            (Ordering::Equal, true) => Tree::Cte(Constant::Infinity(Ordering::Greater)),
            (Ordering::Equal, false) => Tree::Cte(Constant::Infinity(Ordering::Equal)),
          }),

          // ```i^y, y ∈ ℤ```
          // ```i^y =  1, y mod 4 = 0```
          // ```i^y =  i, y mod 4 = 1```
          // ```i^y = -1, y mod 4 = 2```
          // ```i^y = -i, y mod 4 = 3```
          (Tree::Cte(Constant::i), Tree::Num(Number::Int(rhs))) => Ok(match rhs.rem_euclid(Integer::from(4)) {
            Integer::ZERO => Tree::from(1),
            Integer::ONE => Tree::Cte(Constant::i),
            Integer::TWO => Tree::from(-1),
            _ => Tree::Cte(Constant::i).neg(),
          }),

          // ```0^y, y ∈ ℚ```
          // ```0^y =  0, y > 0```
          // ```0^y = ~∞, y < 0```
          // ```0^0 =  ?```
          (Tree::ZERO, Tree::Num(rhs)) => match rhs.num().ord() {
            Ordering::Greater => Ok(Tree::from(0)),
            Ordering::Less => Ok(Tree::Cte(Constant::Infinity(Ordering::Equal))),
            Ordering::Equal => Err(Form {}),
          },

          // ```sqrt(-1) = (-1)^(1/2) = i```
          (Tree::NEG_ONE, Tree::Num(Number::Rat(Rational { num: Integer::ONE, den: Integer::TWO }))) => Ok(Tree::Cte(Constant::i)),
          // ```1^x = x^0 = 1```
          (Tree::ONE, _) | (_, Tree::ZERO) => Ok(Tree::from(1)),
          // ```x^1 = x```
          (lhs, Tree::ONE) => Ok(lhs),

          // ```x ∈ ℚ, y ∈ ℤ```
          (Tree::Num(lhs), Tree::Num(Number::Int(rhs))) => Ok(Tree::Num(lhs.powi(rhs)?)),
          // ```x ∈ ℤ, y ∈ ℚ```
          (Tree::Num(Number::Int(lhs)), Tree::Num(rhs)) => Algebra::trivial_root(lhs, rhs),

          // ```(b^e)^y = b^(e*y), y ∈ ℤ```
          (Tree::Alg(Algebra::BExpr { map: BOp::Pow, arg: (b, e) }), rhs) if rhs.dom().le(&Number::Z) => b.pow(e.mul(rhs)).trivial(),

          // ```(x_1*x_2*...*x_n)^y = x_1^y*x_2^y*...*x_n^y, y ∈ ℤ```
          (Tree::Alg(Algebra::AssocExpr(Assoc { map: AOp::Mul, arg })), Tree::Num(rhs)) if rhs.dom().le(&Number::Z) => {
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
    match rhs.clone().try_root(&lhs.mag) {
      Some(Number::Int(Integer::ONE)) | None => Ok(Tree::from(lhs).pow(Tree::Num(rhs))),
      Some(root) => {
        let root = Tree::Num(root);
        if lhs.is_negative() {
          // ```(-x)^(n/d) = x^(n/d)*(-1)^div(n, d)*(-1)^(mod(n, d)/d)```
          let n = rhs.num();
          let d = rhs.den();
          let (q, r) = (n.clone().div_euclid(d.clone()), n.clone().rem_euclid(d));
          root.mul(Tree::from(-1).pow(Tree::from(q)).mul(Tree::from(-1).pow(Tree::from(Rational::new(r, rhs.den()))))).trivial()
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
  #[inline]
  fn trivial(self) -> SymbolicResult<Tree> {
    let mut flat = Vec::new();
    // Apply associative property.
    let Assoc { map, mut arg } = self.flatten(&mut flat)?;
    // Apply commutative property.
    flat.sort_by(|lhs, rhs| map.cmp_poly(lhs.is_value().cmp(&rhs.is_value()), Ordering::Equal).then(rhs.cmp(lhs)));

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
            return Ok(Tree::ZERO);
          }

          // ```x + z∞ = z∞```
          (AOp::Add, _, Tree::Cte(Constant::Infinity(z))) | (AOp::Add, Tree::Cte(Constant::Infinity(z)), _) => flat.push(Tree::Cte(Constant::Infinity(z))),
          // ```~∞*x = ~∞```
          (AOp::Mul, Tree::Cte(Constant::Infinity(Ordering::Equal)), _) | (AOp::Mul, _, Tree::Cte(Constant::Infinity(Ordering::Equal))) => flat.push(Tree::Cte(Constant::Infinity(Ordering::Equal))),

          // ```z1∞*z2∞ = sgn(z1*z2)∞```
          (AOp::Mul, Tree::Cte(Constant::Infinity(lhs)), Tree::Cte(Constant::Infinity(rhs))) => flat.push(Tree::Cte(Constant::Infinity(Constant::sgn_cmp(lhs, rhs)))),

          // ```x*z∞ = sgn(x*z)∞, x ∈ ℚ```
          (AOp::Mul, Tree::Num(lhs), Tree::Cte(Constant::Infinity(z))) => flat.push(Tree::Cte(Constant::Infinity(Constant::sgn_cmp(lhs.num().ord(), z)))),

          // ```x, y ∈ ℚ```
          (AOp::Add, Tree::Num(lhs), Tree::Num(rhs)) => flat.push(Tree::Num(lhs.add(rhs)?)),
          (AOp::Mul, Tree::Num(lhs), Tree::Num(rhs)) => flat.push(Tree::Num(lhs.mul(rhs)?)),

          // ```x + 0 = x```
          (AOp::Add, lhs, Tree::ZERO) => flat.push(lhs),
          // ```1*x = x```
          (AOp::Mul, Tree::ONE, rhs) => flat.push(rhs),

          (_, lhs, rhs) => {
            let (lhs_base, lhs_coeff) = Self::split(map, &lhs)?;
            let (rhs_base, rhs_coeff) = Self::split(map, &rhs)?;

            let factor = if lhs_base == rhs_base {
              // ```c*x + d*x = (c + d)*x, {c, d} ∈ ℚ``` or
              // ```x^c * x^d = x^(c + d)```
              let coeff = lhs_coeff.add(rhs_coeff).trivial()?;
              Self::merge(map, lhs_base, coeff)?
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

    let tree = match arg.len() {
      0 => map.id(),
      1 => arg.remove(0).trivial()?,
      _ => Tree::assoc(
        map, //.
        arg,
      ),
    };
    Ok(tree)
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
          sarg.into_iter().for_each(|sub| self.arg.push(sub))
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

  /// Split an associative operation.
  /// [`split`](x) = (b, c)
  /// [`split`](x) = [`split`]([`merge`](b, c)) = (b, c)
  fn split(map: AOp, expr: &Tree) -> SymbolicResult<(Tree, Tree)> {
    match (map, &expr) {
      (
        AOp::Add,
        Tree::Alg(Algebra::AssocExpr(Assoc {
          //.
          map: AOp::Mul,
          arg,
        })),
      ) => {
        if let Some((c, b)) = arg.split_first() {
          if matches!(c.as_ref(), Tree::Num(_)) {
            return Ok((
              Tree::assoc(AOp::Mul, b.to_vec()).trivial()?,
              Tree::from(c.clone()), // ```c*b```
            ));
          }
        }
      }
      (AOp::Mul, Tree::Alg(Algebra::BExpr { map: BOp::Pow, arg: (b, c) })) => {
        return Ok((
          Tree::from(b.clone()),
          Tree::from(c.clone()), // ```b^c```
        ));
      }

      _ => {
        //.
      }
    }

    Ok((
      expr.clone(), // ```b```
      Tree::from(1),
    ))
  }

  /// Merge an associative base and coefficient.
  /// [`merge`](b, c) = x
  /// [`merge`](b, c) = [`merge`]([`split`](x)) = x
  fn merge(map: AOp, base: Tree, coeff: Tree) -> SymbolicResult<Tree> {
    if coeff != Tree::ONE {
      match map {
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
