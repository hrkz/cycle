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
  #[inline]
  pub fn fun_trivial(self) -> SymbolicResult<Tree> {
    match self {
      Function::MapExpr {
        //.
        map,
        arg,
      } => {
        let arg: Result<Vec<_>, _> = arg.into_iter().map(|sub| sub.trivial()).collect();
        Ok(Tree::map(
          map, //.
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
          (EOp::ArcTan, Tree::Cte(Constant::Infinity(z))) => Tree::from(Constant::sgn(z)).mul(Tree::Cte(Constant::pi)).div(Tree::from(2)).trivial(),

          // ```sin(0) = arcsin(0) = 0```
          (EOp::Sin | EOp::ArcSin, Tree::ZERO) => Ok(Tree::from(0)),
          // ```cos(0) = 1```
          (EOp::Cos, Tree::ZERO) => Ok(Tree::from(1)),
          // ```tan(0) = arctan(0) = 0```
          (EOp::Tan | EOp::ArcTan, Tree::ZERO) => Ok(Tree::from(0)),

          // ```sin(π) = 0```
          (EOp::Sin, Tree::Cte(Constant::pi)) => Ok(Tree::from(0)),
          // ```cos(π) = -1```
          (EOp::Cos, Tree::Cte(Constant::pi)) => Ok(Tree::from(-1)),
          // ```tan(π) = 0```
          (EOp::Tan, Tree::Cte(Constant::pi)) => Ok(Tree::from(0)),

          // ```arccos(0) = π/2```
          (EOp::ArcCos, Tree::ZERO) => Tree::Cte(Constant::pi).div(Tree::from(2)).trivial(),
          // ```arccos(1) = 0```
          (EOp::ArcCos, Tree::ONE) => Ok(Tree::from(0)),
          // ```arcsin(1) = π/2```
          (EOp::ArcSin, Tree::ONE) => Tree::Cte(Constant::pi).div(Tree::from(2)).trivial(),
          // ```arctan(1) = π/4```
          (EOp::ArcTan, Tree::ONE) => Tree::Cte(Constant::pi).div(Tree::from(4)).trivial(),

          // ```sin(i) = i*sinh(1)```
          // ```cos(i) = cosh(1)```
          // ```tan(i) = i*tanh(1)```
          (EOp::Sin, Tree::Cte(Constant::i)) => Ok(Tree::Cte(Constant::i).mul(Tree::from(1).sinh())),
          (EOp::Cos, Tree::Cte(Constant::i)) => Ok(Tree::from(1).cosh()),
          (EOp::Tan, Tree::Cte(Constant::i)) => Ok(Tree::Cte(Constant::i).mul(Tree::from(1).tanh())),

          // ```sin(arcsin(x)) = x```
          // ```sin(arccos(x)) = sqrt(1 - x^2)```
          // ```sin(arctan(x)) = x/sqrt(1 + x^2)```
          (EOp::Sin, Tree::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => Ok(Tree::from(arg)),
          (EOp::Sin, Tree::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Tree::from(1).sub(arg.pow(Tree::from(2))).sqrt().trivial(),
          (EOp::Sin, Tree::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => arg.clone().div(Tree::from(1).add(arg.pow(Tree::from(2))).sqrt()).trivial(),

          // ```cos(arcsin(x)) = sqrt(1 - x^2)```
          // ```cos(arccos(x)) = x```
          // ```cos(arctan(x)) = 1/sqrt(1 + x^2)```
          (EOp::Cos, Tree::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => Tree::from(1).sub(arg.pow(Tree::from(2))).sqrt().trivial(),
          (EOp::Cos, Tree::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Ok(Tree::from(arg)),
          (EOp::Cos, Tree::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => Tree::from(1).div(Tree::from(1).add(arg.pow(Tree::from(2))).sqrt()).trivial(),

          // ```tan(arcsin(x)) = x/(sqrt(1 - x^2))```
          // ```tan(arccos(x)) = sqrt(1 - x^2)/x```
          // ```tan(arctan(x)) = x```
          (EOp::Tan, Tree::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => arg.clone().div(Tree::from(1).sub(arg.pow(Tree::from(2))).sqrt()).trivial(),
          (EOp::Tan, Tree::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Tree::from(1).sub(arg.clone().pow(Tree::from(2))).sqrt().div(arg).trivial(),
          (EOp::Tan, Tree::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => Ok(Tree::from(arg)),

          // [Hyperbolic identities](https://en.wikipedia.org/wiki/Hyperbolic_functions#Useful_relations)

          // ```sinh(z∞) = arsinh(z∞) = z∞```
          // ```cosh(z∞) = arcosh(z∞) = ∞```
          (EOp::Sinh | EOp::ArSinh, Tree::Cte(Constant::Infinity(z))) => Ok(Tree::Cte(Constant::Infinity(z))),
          (EOp::Cosh | EOp::ArCosh, Tree::Cte(Constant::Infinity(_))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),
          // ```tanh(z∞) = sgn(z)```
          // ```artanh(z∞) = -sgn(z)*π*i/2```
          (EOp::Tanh, Tree::Cte(Constant::Infinity(z))) => Ok(Tree::from(Constant::sgn(z))),
          (EOp::ArTanh, Tree::Cte(Constant::Infinity(z))) => Tree::from(-Constant::sgn(z)).mul(Tree::Cte(Constant::pi)).mul(Tree::Cte(Constant::i)).div(Tree::from(2)).trivial(),

          // ```sinh(0) = arsinh(0) = 0```
          (EOp::Sinh | EOp::ArSinh, Tree::ZERO) => Ok(Tree::from(0)),
          // ```cosh(0) = 1```
          (EOp::Cosh, Tree::ZERO) => Ok(Tree::from(1)),
          // ```tanh(0) = artanh(0) = 0```
          (EOp::Tanh | EOp::ArTanh, Tree::ZERO) => Ok(Tree::from(0)),

          // ```arcosh(0) = π*i/2```
          (EOp::ArCosh, Tree::ZERO) => Tree::Cte(Constant::pi).mul(Tree::Cte(Constant::i)).div(Tree::from(2)).trivial(),
          // ```arcosh(1) = 0```
          (EOp::ArCosh, Tree::ONE) => Ok(Tree::from(0)),
          // ```artanh(1) = ∞```
          (EOp::ArTanh, Tree::ONE) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),

          // ```sinh(arsinh(x)) = x```
          // ```sinh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)```
          // ```sinh(artanh(x)) = x/sqrt(1 - x^2)```
          (EOp::Sinh, Tree::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => Ok(Tree::from(arg)),
          (EOp::Sinh, Tree::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => arg.clone().sub(Tree::from(1)).sqrt().mul(arg.add(Tree::from(1)).sqrt()).trivial(),
          (EOp::Sinh, Tree::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => arg.clone().div(Tree::from(1).sub(arg.pow(Tree::from(2)).sqrt())).trivial(),

          // ```cosh(arsinh(x)) = sqrt(1 + x^2)```
          // ```cosh(arcosh(x)) = x```
          // ```cosh(artanh(x)) = 1/sqrt(1 - x^2)```
          (EOp::Cosh, Tree::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => Tree::from(1).add(arg.pow(Tree::from(2))).sqrt().trivial(),
          (EOp::Cosh, Tree::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => Ok(Tree::from(arg)),
          (EOp::Cosh, Tree::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => Tree::from(1).div(Tree::from(1).sub(arg.pow(Tree::from(2))).sqrt()).trivial(),

          // ```tanh(arsinh(x)) = x/(sqrt(1 + x^2))```
          // ```tanh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)/x```
          // ```tanh(artanh(x)) = x```
          (EOp::Tanh, Tree::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => arg.clone().div(Tree::from(1).add(arg.pow(Tree::from(2))).sqrt()).trivial(),
          (EOp::Tanh, Tree::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => arg.clone().sub(Tree::from(1)).sqrt().mul(arg.clone().add(Tree::from(1)).sqrt()).div(arg).trivial(),
          (EOp::Tanh, Tree::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => Ok(Tree::from(arg)),

          // [Exponential identities](https://en.wikipedia.org/wiki/Exponential_function)

          // ```log(z∞) = ∞```
          // ```exp(-∞) = 0```
          // ```exp(∞) = ∞```
          (EOp::Log, Tree::Cte(Constant::Infinity(_))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),
          (EOp::Exp, Tree::Cte(Constant::Infinity(Ordering::Less))) => Ok(Tree::from(0)),
          (EOp::Exp, Tree::Cte(Constant::Infinity(Ordering::Greater))) => Ok(Tree::Cte(Constant::Infinity(Ordering::Greater))),

          // ```exp(log(x)) = x```
          (EOp::Exp, Tree::Fun(Function::ElemExpr { map: EOp::Log, arg })) => Ok(Tree::from(arg)),

          // ```exp(0) = 1```
          (EOp::Exp, Tree::ZERO) => Ok(Tree::from(1)),
          // ```log(0) = -∞```
          (EOp::Log, Tree::ZERO) => Ok(Tree::Cte(Constant::Infinity(Ordering::Less))),
          // ```log(1) = 0```
          (EOp::Log, Tree::ONE) => Ok(Tree::from(0)),

          (map, arg) => Ok(Tree::elem(
            map, //.
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
        write!(f, "{}({arg})", format!("{map:?}").to_lowercase())
      }

      Function::SpecExpr(map) => match map {
        Special::Gamma(arg) => write!(f, "gamma({arg})"),
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
