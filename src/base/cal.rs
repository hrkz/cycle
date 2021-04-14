use std::fmt;

use crate::{Expr, Form, Symbol, SymbolicResult};

use crate::base::{
  alg::{AOp, Algebra, Assoc, BOp, UOp},
  fun::{EOp, Function},
};

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum CalOp {
  Der,
  Int,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Calculus {
  pub map: CalOp,
  pub arg: Box<Expr>,
  pub var: Vec<Expr>,
}

impl Calculus {
  pub fn trivial(self) -> SymbolicResult<Expr> {
    let op = match self.map {
      // [Rule-based differentiation](https://en.wikipedia.org/wiki/Differentiation_rules)
      // * product
      // * exponential
      // * chain
      // * flatten higher order derivatives
      CalOp::Der => Self::differentiate,
      // [Limited Risch integration](https://en.wikipedia.org/wiki/Risch_algorithm)
      // not implemented
      CalOp::Int => return Ok(Expr::Cal(self)),
    };

    self
      .var
      .into_iter()
      // compose
      .try_fold(*self.arg, |acc, var| {
        var.is_symbol().map_or(Err(Form {}), |var| {
          op(
            acc, //.
            &var,
          )
        })
      })
  }

  fn differentiate(expr: Expr, part: &Symbol) -> SymbolicResult<Expr> {
    match expr.trivial()? {
      // ```∂x/∂x = 1```
      Expr::Sym(sym) if *sym == *part => Ok(Expr::ONE),
      // ```∂y/∂x = 0```
      Expr::Sym(_) | Expr::Cte(_) | Expr::Num(_) => {
        Ok(Expr::ZERO) //.
      }

      Expr::Alg(alg) => {
        match alg {
          Algebra::UExpr {
            //.
            map: UOp::Id,
            arg,
          } => Self::differentiate(*arg, part),

          // exponent rule
          // ```∂(f^g)/∂x = f^g*(∂g/∂x*log(f) + ∂f/∂x*g/f)```
          Algebra::BExpr {
            //.
            map: BOp::Pow,
            arg: (lhs, rhs),
          } => {
            let dl = Self::differentiate(*lhs.clone(), part)?;
            let dr = Self::differentiate(*rhs.clone(), part)?;
            (lhs.clone().pow(*rhs.clone()) * (dr * lhs.clone().log() + dl * *rhs / *lhs)).trivial()
          }

          Algebra::AssocExpr(Assoc {
            //.
            map,
            arg,
          }) => {
            match map {
              // sum rule
              // ```∂(f_1 + f_2 + ... + f_n)/∂x = ∂f_1/∂x + ∂f_2/∂x + ... + ∂f_n/∂x```
              AOp::Add => {
                let sdxi: Result<Vec<_>, _> = arg.into_iter().map(|sub| Self::differentiate(sub, part)).collect();

                Expr::assoc(
                  AOp::Add, //.
                  sdxi?,
                )
              }

              // product rule
              // ```∂(f_1*f_2*...*f_n)/∂x = ∂f_1/∂x*(f_2*...*f_n) + ∂f_2/∂x*(f_1*f_3*...*f_n) + ... + ∂f_n/∂x*(f_1*...*f_n - 1)```
              AOp::Mul => {
                let pdxi: Result<Vec<_>, _> = arg
                  .clone()
                  .into_iter()
                  .enumerate()
                  .map(|(i, sub)| {
                    let mut prod = arg.clone();
                    prod[i] = Self::differentiate(sub, part)?;
                    Ok(Expr::assoc(AOp::Mul, prod))
                  })
                  .collect();

                Expr::assoc(
                  AOp::Add, //.
                  pdxi?,
                )
              }
            }
            .trivial()
          }
        }
      }

      Expr::Fun(Function::ElemExpr {
        //.
        map,
        arg,
      }) => {
        arg
          .clone()
          .chain_rule(
            match map {
              // ```∂(sin(f))/∂x = cos(f)```
              // ```∂(cos(f))/∂x = -sin(f)```
              // ```∂(tan(f))/∂x = 1/cos(f)^2```
              EOp::Sin => arg.cos(),
              EOp::Cos => -arg.sin(),
              EOp::Tan => arg.cos().pow(Expr::from(-2)),

              // ```∂(arcsin(f))/∂x = 1/sqrt(1 - f^2)```
              // ```∂(arccos(f))/∂x = -1/sqrt(1 - f^2)```
              // ```∂(arctan(f))/∂x = 1/(1 + f^2)```
              EOp::ArcSin => Expr::ONE / Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2))),
              EOp::ArcCos => Expr::NEG_ONE / Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2))),
              EOp::ArcTan => Expr::ONE / (Expr::ONE + arg.pow(Expr::from(2))),

              // ```∂(sinh(f))/∂x = cosh(f)```
              // ```∂(cosh(f))/∂x = sinh(f)```
              // ```∂(tanh(f))/∂x = 1/cosh^2(f)```
              EOp::Sinh => arg.cosh(),
              EOp::Cosh => arg.sinh(),
              EOp::Tanh => arg.cosh().pow(Expr::from(-2)),

              // ```∂(arsinh(f))/∂x = 1/sqrt(1 + f^2)```
              // ```∂(arcosh(f))/∂x = 1/(sqrt(f - 1)*sqrt(f + 1))```
              // ```∂(artanh(f))/∂x = 1/(1 - f^2)```
              EOp::ArSinh => Expr::ONE / Expr::sqrt(Expr::ONE + arg.pow(Expr::from(2))),
              EOp::ArCosh => Expr::ONE / (Expr::sqrt(*arg.clone() - Expr::ONE) * Expr::sqrt(*arg + Expr::ONE)),
              EOp::ArTanh => Expr::ONE / (Expr::ONE - arg.pow(Expr::from(2))),

              // ```∂(exp(f))/∂x = exp(f)```
              // ```∂(log(f))/∂x = 1/f```
              EOp::Exp => arg.exp(),
              EOp::Log => Expr::ONE / *arg,
            },
            part,
          )?
          .trivial()
      }

      Expr::Cal(Calculus {
        //.
        map: CalOp::Der,
        arg,
        mut var,
      }) => {
        var.push(Expr::Sym(Symbol::new(&part.name, part.dom)));
        Ok(Expr::Cal(Calculus {
          //.
          map: CalOp::Der,
          arg,
          var,
        }))
      }

      expr => {
        Ok(expr.derivative([Expr::Sym(Symbol::new(&part.name, part.dom))].to_vec()))
        //.
      }
    }
  }

  fn _integrate(_expr: Expr, _part: &Symbol) -> SymbolicResult<Expr> {
    todo!() //.
  }
}

impl fmt::Display for Calculus {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let mut iter = self.var.iter();
    if let Some(v) = iter.next() {
      let var = iter.fold(format!("{}", v), |acc, v| acc + &format!(", {}", v));
      write!(
        //.
        f,
        "{}({}; {})",
        self.map,
        self.arg,
        var
      )?;
    }

    Ok(())
  }
}

impl fmt::Display for CalOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      // ```∂(f; x_1, x_2, ..., x_n)```
      CalOp::Der => write!(
        f,
        "∂" //.
      ),
      // ```∫(f; x_1, x_2, ..., x_n)```
      CalOp::Int => write!(
        f,
        "∫" //.
      ),
    }
  }
}

impl Expr {
  /// ```∂(f(g))/∂x = (∂f/∂x)(g)*∂g/∂x```
  fn chain_rule(self, derivative: Expr, part: &Symbol) -> SymbolicResult<Expr> { Ok(Calculus::differentiate(self, part)? * derivative) }

  /// ```∂f/(∂x_1 ∂x_2 ... ∂x_n)```
  pub fn derivative(self, var: Vec<Expr>) -> Expr { Self::calculus_order(CalOp::Der, Box::new(self), var) }

  /// ```∫ ∫ ... ∫ f dx_1 dx_2 ... dx_n```
  pub fn integral(self, var: Vec<Expr>) -> Expr { Self::calculus_order(CalOp::Int, Box::new(self), var) }

  fn calculus_order(
    //.
    map: CalOp,
    arg: Box<Expr>,
    var: Vec<Expr>,
  ) -> Expr {
    Self::Cal(Calculus {
      //.
      map,
      arg,
      var,
    })
  }
}
