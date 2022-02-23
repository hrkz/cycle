use std::fmt;

use crate::{Edge, Expr, Tree};
use crate::{Symbol, SymbolicResult};

use crate::base::{
  alg::{AOp, Algebra, Assoc, BOp},
  fun::{EOp, Function},
};

/// A list of calculus operators.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum CalOp {
  Der,
  Int,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Calculus {
  pub map: CalOp,
  pub arg: Edge,
  pub var: Vec<Symbol>,
}

impl Calculus {
  /// Apply calculus simplifications.
  #[inline]
  pub fn cal_trivial(self) -> SymbolicResult<Tree> {
    let cal_op = match self.map {
      // [Rule-based differentiation](https://en.wikipedia.org/wiki/Differentiation_rules)
      // * product
      // * exponential
      // * chain
      // * flatten higher order derivatives
      CalOp::Der => Calculus::differentiate,
      // [Limited Risch integration](https://en.wikipedia.org/wiki/Risch_algorithm)
      // not implemented
      CalOp::Int => Calculus::integrate,
    };

    self
      .var
      .iter()
      // compose
      .try_fold(Tree::from(self.arg), |acc, var| {
        cal_op(
          acc, //.
          var,
        )
      })
  }

  #[inline]
  pub(crate) fn differentiate<T: Expr>(expr: T, part: &Symbol) -> SymbolicResult<Tree> {
    match expr.trivial()? {
      // ```∂x/∂x = 1```
      Tree::Sym(sym) if &sym == part => Ok(Tree::from(1)),
      // ```∂y/∂x = 0```
      Tree::Sym(_) | Tree::Cte(_) | Tree::Num(_) => {
        Ok(Tree::from(0)) //.
      }

      Tree::Alg(alg) => {
        match alg {
          Algebra::UExpr {
            //.
            map: _,
            arg,
          } => Self::differentiate(arg, part),

          // exponent rule
          // ```∂(f^g)/∂x = f^g*(∂g/∂x*log(f) + ∂f/∂x*g/f)```
          Algebra::BExpr {
            //.
            map: BOp::Pow,
            arg: (lhs, rhs),
          } => {
            let dl = Self::differentiate(lhs.clone(), part)?;
            let dr = Self::differentiate(rhs.clone(), part)?;
            lhs.clone().pow(rhs.clone()).mul(dr.mul(lhs.clone().log()).add(dl.mul(rhs).div(lhs))).trivial()
          }

          // sum rule
          // ```∂(f_1 + f_2 + ... + f_n)/∂x = ∂f_1/∂x + ∂f_2/∂x + ... + ∂f_n/∂x```
          Algebra::AssocExpr(Assoc {
            //.
            map: AOp::Add,
            arg,
          }) => {
            let sdxi: Result<Vec<_>, _> = arg.into_iter().map(|sub| Ok(Self::differentiate(sub, part)?.edge())).collect();
            Tree::assoc(AOp::Add, sdxi?).trivial()
          }

          // product rule
          // ```∂(f_1*f_2*...*f_n)/∂x = ∂f_1/∂x*(f_2*...*f_n) + ∂f_2/∂x*(f_1*f_3*...*f_n) + ... + ∂f_n/∂x*(f_1*...*f_n - 1)```
          Algebra::AssocExpr(Assoc {
            //.
            map: AOp::Mul,
            arg,
          }) => {
            let pdxi = arg.iter().map(|sub| {
              let dfxi = Self::differentiate(sub.clone(), part)?;
              Ok(dfxi.edge())
            });

            Tree::assoc(
              AOp::Add,
              pdxi.enumerate().try_fold(Vec::with_capacity(arg.len()), |mut acc, (i, dxfi)| {
                let mut prod = arg.clone();
                prod[i] = dxfi?;
                acc.push(Tree::assoc(AOp::Mul, prod).edge());
                Ok(acc)
              })?,
            )
            .trivial()
          }
        }
      }

      Tree::Fun(Function::ElemExpr {
        //.
        map,
        arg,
      }) => {
        let comp = arg.clone();
        let diff = match map {
          // ```∂(sin(f))/∂x = cos(f)```
          // ```∂(cos(f))/∂x = -sin(f)```
          // ```∂(tan(f))/∂x = 1/cos(f)^2```
          EOp::Sin => arg.cos(),
          EOp::Cos => arg.sin().neg(),
          EOp::Tan => arg.cos().pow(Tree::from(-2)),

          // ```∂(arcsin(f))/∂x = 1/sqrt(1 - f^2)```
          // ```∂(arccos(f))/∂x = -1/sqrt(1 - f^2)```
          // ```∂(arctan(f))/∂x = 1/(1 + f^2)```
          EOp::ArcSin => Tree::from(1).div(Tree::from(1).sub(arg.pow(Tree::from(2)))).sqrt(),
          EOp::ArcCos => Tree::from(-1).div(Tree::from(1).sub(arg.pow(Tree::from(2)))).sqrt(),
          EOp::ArcTan => Tree::from(1).div(Tree::from(1).add(arg.pow(Tree::from(2)))),

          // ```∂(sinh(f))/∂x = cosh(f)```
          // ```∂(cosh(f))/∂x = sinh(f)```
          // ```∂(tanh(f))/∂x = 1/cosh^2(f)```
          EOp::Sinh => arg.cosh(),
          EOp::Cosh => arg.sinh(),
          EOp::Tanh => arg.cosh().pow(Tree::from(-2)),

          // ```∂(arsinh(f))/∂x = 1/sqrt(1 + f^2)```
          // ```∂(arcosh(f))/∂x = 1/(sqrt(f - 1)*sqrt(f + 1))```
          // ```∂(artanh(f))/∂x = 1/(1 - f^2)```
          EOp::ArSinh => Tree::from(1).div(Tree::from(1).add(arg.pow(Tree::from(2)))).sqrt(),
          EOp::ArCosh => Tree::from(1).div(arg.clone().sub(Tree::from(1)).sqrt().mul(arg.add(Tree::from(1)).sqrt())),
          EOp::ArTanh => Tree::from(1).div(Tree::from(1).sub(arg.pow(Tree::from(2)))),

          // ```∂(exp(f))/∂x = exp(f)```
          // ```∂(log(f))/∂x = 1/f```
          EOp::Exp => arg.exp(),
          EOp::Log => Tree::from(1).div(arg),
        };

        Tree::chain_rule(comp, diff, part)?.trivial()
      }

      Tree::Cal(Calculus {
        //.
        map: CalOp::Der,
        arg,
        mut var,
      }) => {
        var.push(part.clone());
        Ok(arg.derivative(var))
      }

      expr => {
        Ok(expr.derivative(
          [part.clone()].to_vec(), //.
        ))
      }
    }
  }

  #[inline]
  pub(crate) fn integrate<T: Expr>(_expr: T, _part: &Symbol) -> SymbolicResult<Tree> {
    todo!() //.
  }
}

impl fmt::Display for Calculus {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let mut iter = self.var.iter();
    if let Some(v) = iter.next() {
      let var = iter.fold(format!("{v}"), |acc, v| acc + &format!(", {v}"));
      write!(f, "{}({}, {var})", self.map, self.arg)?;
    }

    Ok(())
  }
}

impl fmt::Display for CalOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      // Differential operator form
      // ```D(f, x_1, x_2, ..., x_n)```
      CalOp::Der => {
        write!(f, "D")
      }
      // Integral operator form
      // ```L(f, x_1, x_2, ..., x_n)```
      CalOp::Int => {
        write!(f, "L")
      }
    }
  }
}

impl Tree {
  /// ```∂(f(g))/∂x = (∂f/∂x)(g)*∂g/∂x```
  pub(crate) fn chain_rule<T: Expr>(arg: T, der: Tree, part: &Symbol) -> SymbolicResult<Tree> {
    Ok(Calculus::differentiate(arg, part)?.mul(der))
  }

  pub(crate) fn calculus_order(
    //.
    map: CalOp,
    arg: Edge,
    var: Vec<Symbol>,
  ) -> Tree {
    Tree::Cal(Calculus {
      //.
      map,
      arg,
      var,
    })
  }
}
