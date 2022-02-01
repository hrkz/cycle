use std::cmp::Ordering;
use std::fmt;

use crate::{Constant, Form, Symbol, SymbolicResult};
use crate::{Edge, Expr, Tree};

/// A list of elementary operations.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum EOp {
  /// Sine.
  Sin,
  /// Cosine.
  Cos,
  /// Tangent.
  Tan,
  /// Inverse sine.
  ArcSin,
  /// Inverse cosine.
  ArcCos,
  /// Inverse tangent.
  ArcTan,

  /// Hyperbolic sine.
  Sinh,
  /// Hyperbolic cosine.
  Cosh,
  /// Hyperbolic tangent.
  Tanh,
  /// Inverse hyperbolic sine.
  ArSinh,
  /// Inverse hyperbolic cosine.
  ArCosh,
  /// Inverse hyperbolic tangent.
  ArTanh,

  /// Exponential.
  Exp,
  /// Logarithm.
  Log,
}

/// A list of special functions.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub enum Special {
  /// Gamma Γ(x).
  Gamma(Edge),
  // Polygamma ψ(n, z).
  //Polygamma(Edge, Edge),
  // Beta Β(x, y).
  //Beta(Edge, Edge),
  // Error function.
  //Erf(Edge),
  // Abs.
  //Abs(Edge),
  // Sgn.
  //Sgn(Edge),

  // Real.
  //Real(Edge),
  // Imag.
  //Imag(Edge),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Function {
  ElemExpr {
    map: EOp,
    arg: Edge,
  },

  SpecExpr(
    Special, //.
  ),

  MapExpr {
    map: Symbol,
    arg: Vec<Tree>,
  },
}

impl Function {
  /// Apply functional simplifications.
  pub fn fun_trivial(&self) -> SymbolicResult<Tree> {
    match self {
      Function::MapExpr {
        //.
        map,
        arg,
      } => {
        let arg: Result<Vec<Tree>, _> = arg.iter().map(|sub| sub.trivial()).collect();
        Ok(Tree::map(
          map.clone(), //.
          arg?,
        ))
      }

      Function::ElemExpr {
        //.
        map,
        arg,
      } => {
        match (map, arg.trivial()?) {
          (_, Tree::Cte(Constant::Infinity(Ordering::Equal))) => Err(Form {}),

          // [Trigonometric identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities)

          // ```arctan(z∞) = sgn(z)*π/2```
          (EOp::ArcTan, Tree::Cte(Constant::Infinity(z))) => Tree::from(Constant::dir_cmp(z)).mul(Tree::Cte(Constant::Pi)).mul(Tree::HALF).trivial(),

          // ```sin(0) = arcsin(0) = 0```
          (EOp::Sin | EOp::ArcSin, Tree::ZERO) => Ok(Tree::ZERO),
          // ```cos(0) = 1```
          (EOp::Cos, Tree::ZERO) => Ok(Tree::ONE),
          // ```tan(0) = arctan(0) = 0```
          (EOp::Tan | EOp::ArcTan, Tree::ZERO) => Ok(Tree::ZERO),

          // ```sin(π) = 0```
          (EOp::Sin, Tree::Cte(Constant::Pi)) => Ok(Tree::ZERO),
          // ```cos(π) = -1```
          (EOp::Cos, Tree::Cte(Constant::Pi)) => Ok(Tree::NEG_ONE),
          // ```tan(π) = 0```
          (EOp::Tan, Tree::Cte(Constant::Pi)) => Ok(Tree::ZERO),

          // ```arccos(0) = π/2```
          (EOp::ArcCos, Tree::ZERO) => Tree::Cte(Constant::Pi).mul(Tree::HALF).trivial(),
          // ```arcsin(1) = π/2```
          (EOp::ArcSin, Tree::ONE) => Tree::Cte(Constant::Pi).mul(Tree::HALF).trivial(),
          // ```arccos(1) = 0```
          (EOp::ArcCos, Tree::ONE) => Ok(Tree::ZERO),
          // ```arctan(1) = π/4```
          (EOp::ArcTan, Tree::ONE) => Tree::Cte(Constant::Pi).mul(Tree::QUARTER).trivial(),

          // ```sin(I) = I*sinh(1)```
          // ```cos(I) = cosh(1)```
          // ```tan(I) = I*tanh(1)```
          (EOp::Sin, Tree::Cte(Constant::I)) => Ok(Tree::Cte(Constant::I).mul(Tree::ONE.sinh())),
          (EOp::Cos, Tree::Cte(Constant::I)) => Ok(Tree::ONE.cosh()),
          (EOp::Tan, Tree::Cte(Constant::I)) => Ok(Tree::Cte(Constant::I).mul(Tree::ONE.tanh())),

          // ```sin(arcsin(x)) = x```
          // ```sin(arccos(x)) = sqrt(1 - x^2)```
          // ```sin(arctan(x)) = x/sqrt(1 + x^2)```
          (EOp::Sin, Tree::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => Ok(Tree::from(&arg)),
          (EOp::Sin, Tree::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Tree::ONE.sub(arg.pow(Tree::from(2))).sqrt().trivial(),
          (EOp::Sin, Tree::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => arg.clone().div(Tree::ONE.add(arg.pow(Tree::from(2))).sqrt()).trivial(),

          // ```cos(arcsin(x)) = sqrt(1 - x^2)```
          // ```cos(arccos(x)) = x```
          // ```cos(arctan(x)) = 1/sqrt(1 + x^2)```
          (EOp::Cos, Tree::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => Tree::ONE.sub(arg.pow(Tree::from(2))).sqrt().trivial(),
          (EOp::Cos, Tree::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Ok(Tree::from(&arg)),
          (EOp::Cos, Tree::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => Tree::ONE.div(Tree::ONE.add(arg.pow(Tree::from(2))).sqrt()).trivial(),

          // ```tan(arcsin(x)) = x/(sqrt(1 - x^2))```
          // ```tan(arccos(x)) = sqrt(1 - x^2)/x```
          // ```tan(arctan(x)) = x```
          (EOp::Tan, Tree::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => arg.clone().div(Tree::ONE.sub(arg.pow(Tree::from(2))).sqrt()).trivial(),
          (EOp::Tan, Tree::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Tree::ONE.sub(arg.clone().pow(Tree::from(2))).sqrt().div(arg).trivial(),
          (EOp::Tan, Tree::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => Ok(Tree::from(&arg)),

          // [Hyperbolic identities](https://en.wikipedia.org/wiki/Hyperbolic_functions#Useful_relations)

          // ```sinh(z∞) = arsinh(z∞) = z∞```
          // ```cosh(z∞) = arcosh(z∞) = ∞```
          (EOp::Sinh | EOp::ArSinh, Tree::Cte(Constant::Infinity(z))) => Ok(Tree::Cte(Constant::Infinity(z))),
          (EOp::Cosh | EOp::ArCosh, Tree::Cte(Constant::Infinity(_))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),
          // ```tanh(z∞) = sgn(z)```
          // ```artanh(z∞) = -sgn(z)*π*I/2```
          (EOp::Tanh, Tree::Cte(Constant::Infinity(z))) => Ok(Tree::from(Constant::dir_cmp(z))),
          (EOp::ArTanh, Tree::Cte(Constant::Infinity(z))) => Tree::from(-Constant::dir_cmp(z)).mul(Tree::Cte(Constant::Pi)).mul(Tree::Cte(Constant::I)).mul(Tree::HALF).trivial(),

          // ```sinh(0) = arsinh(0) = 0```
          (EOp::Sinh | EOp::ArSinh, Tree::ZERO) => Ok(Tree::ZERO),
          // ```cosh(0) = 1```
          (EOp::Cosh, Tree::ZERO) => Ok(Tree::ONE),
          // ```tanh(0) = artanh(0) = 0```
          (EOp::Tanh | EOp::ArTanh, Tree::ZERO) => Ok(Tree::ZERO),

          // ```arcosh(0) = π*I/2```
          (EOp::ArCosh, Tree::ZERO) => Tree::Cte(Constant::Pi).mul(Tree::Cte(Constant::I)).mul(Tree::HALF).trivial(),
          // ```arcosh(1) = 0```
          (EOp::ArCosh, Tree::ONE) => Ok(Tree::ZERO),
          // ```artanh(1) = ∞```
          (EOp::ArTanh, Tree::ONE) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),

          // ```sinh(arsinh(x)) = x```
          // ```sinh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)```
          // ```sinh(artanh(x)) = x/sqrt(1 - x^2)```
          (EOp::Sinh, Tree::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => Ok(Tree::from(&arg)),
          (EOp::Sinh, Tree::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => arg.clone().sub(Tree::ONE).sqrt().mul(arg.add(Tree::ONE).sqrt()).trivial(),
          (EOp::Sinh, Tree::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => arg.clone().div(Tree::ONE.sub(arg.pow(Tree::from(2)).sqrt())).trivial(),

          // ```cosh(arsinh(x)) = sqrt(1 + x^2)```
          // ```cosh(arcosh(x)) = x```
          // ```cosh(artanh(x)) = 1/sqrt(1 - x^2)```
          (EOp::Cosh, Tree::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => Tree::ONE.add(arg.pow(Tree::from(2))).sqrt().trivial(),
          (EOp::Cosh, Tree::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => Ok(Tree::from(&arg)),
          (EOp::Cosh, Tree::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => Tree::ONE.div(Tree::ONE.sub(arg.pow(Tree::from(2))).sqrt()).trivial(),

          // ```tanh(arsinh(x)) = x/(sqrt(1 + x^2))```
          // ```tanh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)/x```
          // ```tanh(artanh(x)) = x```
          (EOp::Tanh, Tree::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => arg.clone().div(Tree::ONE.add(arg.pow(Tree::from(2))).sqrt()).trivial(),
          (EOp::Tanh, Tree::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => arg.clone().sub(Tree::ONE).sqrt().mul(arg.clone().add(Tree::ONE).sqrt()).div(arg).trivial(),
          (EOp::Tanh, Tree::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => Ok(Tree::from(&arg)),

          // [Exponential identities](https://en.wikipedia.org/wiki/Exponential_function)

          // ```log(z∞) = ∞```
          // ```exp(-∞) = 0```
          // ```exp(∞) = ∞```
          (EOp::Log, Tree::Cte(Constant::Infinity(_))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),
          (EOp::Exp, Tree::Cte(Constant::Infinity(Ordering::Less))) => Ok(Tree::ZERO),
          (EOp::Exp, Tree::Cte(Constant::Infinity(Ordering::Greater))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),

          // ```exp(log(x)) = x```
          (EOp::Exp, Tree::Fun(Function::ElemExpr { map: EOp::Log, arg })) => Ok(Tree::from(&arg)),

          // ```exp(0) = 1```
          (EOp::Exp, Tree::ZERO) => Ok(Tree::ONE),
          // ```log(0) = -∞```
          (EOp::Log, Tree::ZERO) => Ok(Tree::Cte(Constant::Infinity(Ordering::Less))),
          // ```log(1) = 0```
          (EOp::Log, Tree::ONE) => Ok(Tree::ZERO),

          // ```log(1/x) = -log(x), x ∈ ℕ```
          (EOp::Log, Tree::Num(rhs)) if rhs.num().eq(&1) => Ok(Tree::log(Tree::from(rhs.den())).neg()),

          (map, arg) => Ok(Tree::elem(
            *map, //.
            arg.edge(),
          )),
        }
      }

      Function::SpecExpr(map) => match map {
        Special::Gamma(arg) => Ok(arg.trivial()?.gamma()),
      },
    }
  }
}

impl fmt::Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Function::ElemExpr {
        //.
        map,
        arg,
      } => {
        write!(f, "{map:?}({arg})")
      }

      Function::SpecExpr(map) => match map {
        Special::Gamma(arg) => write!(f, "Gamma({arg})"),
      },

      Function::MapExpr {
        //.
        map,
        arg,
      } => {
        write!(f, "{map}(",)?;
        let mut iter = arg.iter();
        if let Some(e) = iter.next() {
          let arg = iter.fold(format!("{e}"), |acc, e| acc + &format!(", {e}"));
          write!(f, "{arg}")?;
        }
        write!(
          f, //.
          ")"
        )
      }
    }
  }
}

impl Tree {
  pub(crate) fn elem(map: EOp, arg: Edge) -> Tree {
    Tree::Fun(Function::ElemExpr {
      //.
      map,
      arg,
    })
  }
}
