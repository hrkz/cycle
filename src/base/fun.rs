use std::fmt;

use crate::{Constant, Expr, Form, Number, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub enum ElemOp {
  // Trigonometric
  Sin,
  Cos,
  Tan,
  ArcSin,
  ArcCos,
  ArcTan,

  // Hyperbolic
  Sinh,
  Cosh,
  Tanh,
  ArSinh,
  ArCosh,
  ArTanh,

  // Exponential
  Exp,
  Log,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Special {
  /// ```(f ∘ g)(x)```
  Comp(Box<Expr>, Box<Expr>),

  // Abs
  //Abs(Box<Expr>),

  // Combinatorial
  Fact(Box<Expr>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Function {
  ElemExpr {
    map: ElemOp,
    arg: Box<Expr>,
  },

  SpecExpr(
    //.
    Special,
  ),

  MapExpr {
    map: String,
    arg: Vec<Expr>,
  },
}

impl Function {
  pub fn trivial(self) -> SymbolicResult<Expr> {
    match self {
      Function::ElemExpr {
        //.
        map,
        arg,
      } => {
        match (map, arg.trivial()?) {
          (_, Expr::Cte(Constant::Infinity(0))) => Err(Form {}),

          (_, Expr::Fun(Function::ElemExpr { map: rhs, arg })) if map.inverse().map_or(false, |inv| inv.eq(&rhs)) => {
            // inverse functions
            Ok(*arg)
          }

          // [Trigonometric identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities)
          //
          // Using the Pythagorean theorem
          // ```sin(x)^2 + cos(x)^2 = 1```
          // which can be solved for sin, cos
          // ```sin(x) = +- sqrt(1 - cos(x)^2)```
          // ```cos(x) = +- sqrt(1 - sin(x)^2)```
          // and a right-angle triangle, we have
          //
          //
          //            |\
          //            | \
          //            |  \
          //            |   \
          //            |    \
          //            |     \  1
          //     sin x  |      \
          //            |       \
          //            |        \
          //            |___      \
          //            |   |   x  \
          //            |___|_______\
          //
          //                cos x
          //

          // ```arctan(_∞) = sgn(_∞)*π/2```
          (ElemOp::ArcTan, Expr::Cte(Constant::Infinity(z))) => (Expr::Num(Number::Z(z)) * Expr::Cte(Constant::pi) * Expr::HALF).trivial(),

          // ```sin(0) = arcsin(0) = 0```
          (ElemOp::Sin | ElemOp::ArcSin, Expr::ZERO) => Ok(Expr::ZERO),
          // ```cos(0) = 1```
          (ElemOp::Cos, Expr::ZERO) => Ok(Expr::ONE),
          // ```tan(0) = arctan(0) = 0```
          (ElemOp::Tan | ElemOp::ArcTan, Expr::ZERO) => Ok(Expr::ZERO),

          // ```sin(π) = 0```
          (ElemOp::Sin, Expr::Cte(Constant::pi)) => Ok(Expr::ZERO),
          // ```cos(π) = -1```
          (ElemOp::Cos, Expr::Cte(Constant::pi)) => Ok(Expr::NEG_ONE),
          // ```tan(π) = 0```
          (ElemOp::Tan, Expr::Cte(Constant::pi)) => Ok(Expr::ZERO),

          // ```arccos(0) = π/2```
          (ElemOp::ArcCos, Expr::ZERO) => (Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
          // ```arcsin(1) = π/2```
          (ElemOp::ArcSin, Expr::ONE) => (Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
          // ```arccos(1) = 0```
          (ElemOp::ArcCos, Expr::ONE) => Ok(Expr::ZERO),
          // ```arctan(1) = π/4```
          (ElemOp::ArcTan, Expr::ONE) => (Expr::Cte(Constant::pi) * Expr::QUARTER).trivial(),

          // ```sin(I) = I*sinh(1)```
          // ```cos(I) = I*cosh(1)```
          // ```tan(I) = I*tanh(1)```
          (ElemOp::Sin, Expr::Cte(Constant::I)) => Ok(Expr::Cte(Constant::I) * Expr::sinh(Expr::ONE)),
          (ElemOp::Cos, Expr::Cte(Constant::I)) => Ok(Expr::cosh(Expr::ONE)),
          (ElemOp::Tan, Expr::Cte(Constant::I)) => Ok(Expr::Cte(Constant::I) * Expr::tanh(Expr::ONE)),

          // ```sin(arccos(x)) = sqrt(1 - x^2)```
          // ```sin(arctan(x)) = x/sqrt(1 + x^2)```
          (ElemOp::Sin, Expr::Fun(Function::ElemExpr { map: ElemOp::ArcCos, arg })) => Expr::sqrt(Expr::ONE - arg.pow(Expr::Num(Number::Z(2)))).trivial(),
          (ElemOp::Sin, Expr::Fun(Function::ElemExpr { map: ElemOp::ArcTan, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE + arg.pow(Expr::Num(Number::Z(2))))).trivial(),

          // ```cos(arcsin(x)) = sqrt(1 - x^2)```
          // ```cos(arctan(x)) = 1/sqrt(1 + x^2)```
          (ElemOp::Cos, Expr::Fun(Function::ElemExpr { map: ElemOp::ArcSin, arg })) => Expr::sqrt(Expr::ONE - arg.pow(Expr::Num(Number::Z(2)))).trivial(),
          (ElemOp::Cos, Expr::Fun(Function::ElemExpr { map: ElemOp::ArcTan, arg })) => (Expr::ONE / Expr::sqrt(Expr::ONE + arg.pow(Expr::Num(Number::Z(2))))).trivial(),

          // ```tan(arcsin(x)) = x/(sqrt(1 - x^2))```
          // ```tan(arccos(x)) = sqrt(1 - x^2)/x```
          (ElemOp::Tan, Expr::Fun(Function::ElemExpr { map: ElemOp::ArcSin, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE - arg.pow(Expr::Num(Number::Z(2))))).trivial(),
          (ElemOp::Tan, Expr::Fun(Function::ElemExpr { map: ElemOp::ArcCos, arg })) => (Expr::sqrt(Expr::ONE - arg.clone().pow(Expr::Num(Number::Z(2)))) / *arg).trivial(),

          // [Hyperbolic identities](https://en.wikipedia.org/wiki/Hyperbolic_functions#Useful_relations)
          //
          // This is less trivial than for trigonometric functions, but the equivalent gives
          // ```sinh(x)^2 - cosh(x)^2 = -1```
          // which can also be solved for sinh and cosh
          // ```sinh(x) = +- sqrt(cosh(x)^2 - 1)```
          // ```cosh(x) = +- sqrt(sinh(x)^2 - 1)```
          // and the same also applies to the hyperbolic triangle,
          //
          //
          //        |                 /
          //        |  cosh x     / /
          //        |          /  /
          //        |       /   /
          //        |    /    /
          //        |  / x/2 /     sinh x
          //        |/______|
          //        |        \
          //        |         \
          //        |           \
          //        |             \
          //        |               \
          //        |                 \
          //

          // ```sinh(_∞) = arsinh(_∞) = _∞```
          // ```cosh(_∞) = arcosh(_∞) = -sgn(_∞)*_∞```
          (ElemOp::Sinh | ElemOp::ArSinh, Expr::Cte(Constant::Infinity(z))) => Ok(Expr::Cte(Constant::Infinity(z))),
          (ElemOp::Cosh | ElemOp::ArCosh, Expr::Cte(Constant::Infinity(_))) => Ok(Expr::Cte(Constant::Infinity(1))),
          // ```tanh(_∞) = sgn(_)```
          // ```artanh(_∞) = -sgn(_)*π*I/2```
          (ElemOp::Tanh, Expr::Cte(Constant::Infinity(z))) => Ok(Expr::Num(Number::Z(z))),
          (ElemOp::ArTanh, Expr::Cte(Constant::Infinity(z))) => (Expr::Num(Number::Z(-z)) * Expr::Cte(Constant::pi) * Expr::Cte(Constant::I) * Expr::HALF).trivial(),

          // ```sinh(0) = arsinh(0) = 0```
          (ElemOp::Sinh | ElemOp::ArSinh, Expr::ZERO) => Ok(Expr::ZERO),
          // ```cosh(0) = 1```
          (ElemOp::Cosh, Expr::ZERO) => Ok(Expr::ONE),
          // ```tanh(0) = artanh(0) = 0```
          (ElemOp::Tanh | ElemOp::ArTanh, Expr::ZERO) => Ok(Expr::ZERO),

          // ```arcosh(0) = I*π/2```
          (ElemOp::ArCosh, Expr::ZERO) => (Expr::Cte(Constant::I) * Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
          // ```arcosh(1) = 0```
          (ElemOp::ArCosh, Expr::ONE) => Ok(Expr::ZERO),
          // ```artanh(1) = ∞```
          (ElemOp::ArTanh, Expr::ONE) => Ok(Expr::Cte(Constant::Infinity(1))),

          // ```sinh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)```
          // ```sinh(artanh(x)) = x/sqrt(1 - x^2)```
          (ElemOp::Sinh, Expr::Fun(Function::ElemExpr { map: ElemOp::ArCosh, arg })) => (Expr::sqrt(*arg.clone() - Expr::ONE) * Expr::sqrt(*arg + Expr::ONE)).trivial(),
          (ElemOp::Sinh, Expr::Fun(Function::ElemExpr { map: ElemOp::ArTanh, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE - arg.pow(Expr::Num(Number::Z(2))))).trivial(),

          // ```cosh(arsinh(x)) = sqrt(1 + x^2)```
          // ```cosh(artanh(x)) = 1/sqrt(1 - x^2)```
          (ElemOp::Cosh, Expr::Fun(Function::ElemExpr { map: ElemOp::ArSinh, arg })) => Expr::sqrt(Expr::ONE + arg.pow(Expr::Num(Number::Z(2)))).trivial(),
          (ElemOp::Cosh, Expr::Fun(Function::ElemExpr { map: ElemOp::ArTanh, arg })) => (Expr::ONE / Expr::sqrt(Expr::ONE - arg.pow(Expr::Num(Number::Z(2))))).trivial(),

          // ```tanh(arsinh(x)) = x/(sqrt(1 + x^2))```
          // ```tanh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)/x```
          (ElemOp::Tanh, Expr::Fun(Function::ElemExpr { map: ElemOp::ArSinh, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE + arg.pow(Expr::Num(Number::Z(2))))).trivial(),
          (ElemOp::Tanh, Expr::Fun(Function::ElemExpr { map: ElemOp::ArCosh, arg })) => (Expr::sqrt(*arg.clone() - Expr::ONE) * Expr::sqrt(*arg.clone() + Expr::ONE) / *arg).trivial(),

          // [Exponential identities](https://en.wikipedia.org/wiki/Exponential_function)
          //

          // ```log(_∞) = ∞```
          // ```exp(-∞) = 0```
          // ```exp(∞) = ∞```
          (ElemOp::Log, Expr::Cte(Constant::Infinity(_))) => Ok(Expr::Cte(Constant::Infinity(1))),
          (ElemOp::Exp, Expr::Cte(Constant::Infinity(-1))) => Ok(Expr::ZERO),
          (ElemOp::Exp, Expr::Cte(Constant::Infinity(1))) => Ok(Expr::Cte(Constant::Infinity(1))),

          // ```exp(0) = 1```
          (ElemOp::Exp, Expr::ZERO) => Ok(Expr::ONE),
          // ```log(0) = -∞```
          (ElemOp::Log, Expr::ZERO) => Ok(Expr::Cte(Constant::Infinity(-1))),
          // ```log(1) = 0```
          (ElemOp::Log, Expr::ONE) => Ok(Expr::ZERO),

          // ```log(1/x) = -log(x), x ∈ ℕ```
          (ElemOp::Log, Expr::Num(rhs)) if rhs.num().eq(&1) => Ok(-Expr::log(Expr::Num(Number::Z(rhs.den())))),

          (map, arg) => {
            Ok(arg.elem(map)) //.
          }
        }
      }

      Function::MapExpr {
        //.
        map,
        arg,
      } => {
        let arg: Result<Vec<Expr>, _> = arg.into_iter().map(|x| x.trivial()).collect();
        Ok(Expr::Fun(Function::MapExpr {
          //.
          map,
          arg: arg?,
        }))
      }

      _ => {
        Ok(Expr::Fun(self)) //.
      }
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
        write!(
          //.
          f,
          "{}({})",
          format!("{:?}", map).to_lowercase(),
          arg
        )
      }

      Function::SpecExpr(spe) => write!(f, "{}", spe),

      Function::MapExpr {
        //.
        map,
        arg,
      } => {
        let mut iter = arg.iter();
        if let Some(e) = iter.next() {
          let args = iter.fold(format!("{}", e), |acc, e| acc + &format!(", {}", e));
          write!(
            //.
            f,
            "{}({})",
            map,
            args
          )
        } else {
          write!(
            //.
            f,
            "{}()",
            map
          )
        }
      }
    }
  }
}

impl fmt::Display for Special {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      // Function composition
      // ```f : X -> Y```
      // ```g : Y -> Z```
      // ```g ∘ f : X -> Z```
      // ```(g ∘ f)(x) = g(f(x))```
      // convenience for function nesting
      Special::Comp(lhs, rhs) => write!(
        //.
        f,
        "{} ∘ {}",
        lhs,
        rhs
      ),

      // Factorial
      // expressed with multiplications
      Special::Fact(arg) => write!(
        //.
        f,
        "{}!",
        arg
      ),
    }
  }
}

impl ElemOp {
  fn inverse(self) -> Option<Self> {
    match self {
      // ```sin(arcsin(x)) = x```
      // ```cos(arccos(x)) = x```
      // ```tan(arctan(x)) = x```
      ElemOp::Sin => Some(ElemOp::ArcSin),
      ElemOp::Cos => Some(ElemOp::ArcCos),
      ElemOp::Tan => Some(ElemOp::ArcTan),

      // ```sinh(arsinh(x)) = x```
      // ```cosh(arcosh(x)) = x```
      // ```tanh(artanh(x)) = x```
      ElemOp::Sinh => Some(ElemOp::ArSinh),
      ElemOp::Cosh => Some(ElemOp::ArCosh),
      ElemOp::Tanh => Some(ElemOp::ArTanh),

      // ```exp(log(x)) = x```
      ElemOp::Exp => Some(ElemOp::Log),

      _ => None,
    }
  }
}

impl Expr {
  /// ```sin(x)```
  pub fn r#sin(self) -> Self { self.elem(ElemOp::Sin) }
  /// ```cos(x)```
  pub fn r#cos(self) -> Self { self.elem(ElemOp::Cos) }
  /// ```tan(x)```
  pub fn r#tan(self) -> Self { self.elem(ElemOp::Tan) }

  /// ```arcsin(x)```
  pub fn r#arcsin(self) -> Self { self.elem(ElemOp::ArcSin) }
  /// ```arccos(x)```
  pub fn r#arccos(self) -> Self { self.elem(ElemOp::ArcCos) }
  /// ```arctan(x)```
  pub fn r#arctan(self) -> Self { self.elem(ElemOp::ArcTan) }

  /// ```sinh(x)```
  pub fn r#sinh(self) -> Self { self.elem(ElemOp::Sinh) }
  /// ```cosh(x)```
  pub fn r#cosh(self) -> Self { self.elem(ElemOp::Cosh) }
  /// ```tanh(x)```
  pub fn r#tanh(self) -> Self { self.elem(ElemOp::Tanh) }

  /// ```arsinh(x)```
  pub fn r#arsinh(self) -> Self { self.elem(ElemOp::ArSinh) }
  /// ```arcosh(x)```
  pub fn r#arcosh(self) -> Self { self.elem(ElemOp::ArCosh) }
  /// ```artanh(x)```
  pub fn r#artanh(self) -> Self { self.elem(ElemOp::ArTanh) }

  /// ```exp(x)```
  pub fn r#exp(self) -> Self { self.elem(ElemOp::Exp) }
  /// ```log(x)```
  pub fn r#log(self) -> Self { self.elem(ElemOp::Log) }

  /// ```x!```
  pub fn r#fact(self) -> Self { Self::Fun(Function::SpecExpr(Special::Fact(Box::new(self)))) }

  /// ```map(x_1, ..., x_n)```
  pub fn r#map(map_str: &str, arg: Vec<Expr>) -> Self {
    let map = map_str.replace(&[' ', '+', '-', '*', '/', '^', '=', '(', ')', '{', '}', '#', '~'][..], "");
    // any non-whitespace, non-special character
    assert_eq!(map, map_str);

    Self::Fun(Function::MapExpr {
      //.
      map,
      arg,
    })
  }

  fn r#elem(self, map: ElemOp) -> Self {
    Self::Fun(Function::ElemExpr {
      //.
      map,
      arg: Box::new(self),
    })
  }
}
