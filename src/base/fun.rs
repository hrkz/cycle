use std::fmt;

use crate::{Constant, Expr, Form, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub enum EOp {
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
  Comp(
    //.
    Box<Expr>,
    Box<Expr>,
  ),

  // Gamma Γ(x)
  //Gamma(Box<Expr>),
  // Polygamma ψ(n, z)
  //Polygamma(Box<Expr>, Box<Expr>),
  // Beta Β(x, y)
  //Beta(Box<Expr>, Box<Expr>),
  // Error function erf(z)
  //Erf(Box<Expr>),
  /// Factorial
  Fact(Box<Expr>),
  // Abs
  //Abs(Box<Expr>),
  // Sgn
  //Sgn(Box<Expr>),

  // Real
  //Real(Box<Expr>),
  // Imag
  //Imag(Box<Expr>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Function {
  ElemExpr {
    map: EOp,
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

      Function::ElemExpr {
        //.
        map,
        arg,
      } => {
        match (map, arg.trivial()?) {
          (_, Expr::Cte(Constant::Infinity(0))) => Err(Form {}),

          // [Trigonometric identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities)
          //
          // The basic relationship between the sine and the cosine is given by the Pythagorean identity:
          // ```sin(x)^2 + cos(x)^2 = 1```
          //
          // which can be solved either for sin or cos:
          // * ```sin(x) = +- sqrt(1 - cos(x)^2)```
          // * ```cos(x) = +- sqrt(1 - sin(x)^2)```
          //
          // on the right-angle triangle,
          // ```sin(x) = opposite / hypothenuse, cos(x) = adjacent / hypothenuse, tan(x) = sin(x) / cos(x) = opposite / adjacent```
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
          //

          // ```arctan(_∞) = sgn(_∞)*π/2```
          (EOp::ArcTan, Expr::Cte(Constant::Infinity(z))) => (Expr::from(z) * Expr::Cte(Constant::pi) * Expr::HALF).trivial(),

          // ```sin(0) = arcsin(0) = 0```
          (EOp::Sin | EOp::ArcSin, Expr::ZERO) => Ok(Expr::ZERO),
          // ```cos(0) = 1```
          (EOp::Cos, Expr::ZERO) => Ok(Expr::ONE),
          // ```tan(0) = arctan(0) = 0```
          (EOp::Tan | EOp::ArcTan, Expr::ZERO) => Ok(Expr::ZERO),

          // ```sin(π) = 0```
          (EOp::Sin, Expr::Cte(Constant::pi)) => Ok(Expr::ZERO),
          // ```cos(π) = -1```
          (EOp::Cos, Expr::Cte(Constant::pi)) => Ok(Expr::NEG_ONE),
          // ```tan(π) = 0```
          (EOp::Tan, Expr::Cte(Constant::pi)) => Ok(Expr::ZERO),

          // ```arccos(0) = π/2```
          (EOp::ArcCos, Expr::ZERO) => (Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
          // ```arcsin(1) = π/2```
          (EOp::ArcSin, Expr::ONE) => (Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
          // ```arccos(1) = 0```
          (EOp::ArcCos, Expr::ONE) => Ok(Expr::ZERO),
          // ```arctan(1) = π/4```
          (EOp::ArcTan, Expr::ONE) => (Expr::Cte(Constant::pi) * Expr::QUARTER).trivial(),

          // ```sin(I) = I*sinh(1)```
          // ```cos(I) = I*cosh(1)```
          // ```tan(I) = I*tanh(1)```
          (EOp::Sin, Expr::Cte(Constant::I)) => Ok(Expr::Cte(Constant::I) * Expr::sinh(Expr::ONE)),
          (EOp::Cos, Expr::Cte(Constant::I)) => Ok(Expr::cosh(Expr::ONE)),
          (EOp::Tan, Expr::Cte(Constant::I)) => Ok(Expr::Cte(Constant::I) * Expr::tanh(Expr::ONE)),

          // ```sin(arcsin(x)) = x```
          // ```sin(arccos(x)) = sqrt(1 - x^2)```
          // ```sin(arctan(x)) = x/sqrt(1 + x^2)```
          (EOp::Sin, Expr::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => Ok(*arg),
          (EOp::Sin, Expr::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2))).trivial(),
          (EOp::Sin, Expr::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE + arg.pow(Expr::from(2)))).trivial(),

          // ```cos(arcsin(x)) = sqrt(1 - x^2)```
          // ```cos(arccos(x)) = x```
          // ```cos(arctan(x)) = 1/sqrt(1 + x^2)```
          (EOp::Cos, Expr::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2))).trivial(),
          (EOp::Cos, Expr::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => Ok(*arg),
          (EOp::Cos, Expr::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => (Expr::ONE / Expr::sqrt(Expr::ONE + arg.pow(Expr::from(2)))).trivial(),

          // ```tan(arcsin(x)) = x/(sqrt(1 - x^2))```
          // ```tan(arccos(x)) = sqrt(1 - x^2)/x```
          // ```tan(arctan(x)) = x```
          (EOp::Tan, Expr::Fun(Function::ElemExpr { map: EOp::ArcSin, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2)))).trivial(),
          (EOp::Tan, Expr::Fun(Function::ElemExpr { map: EOp::ArcCos, arg })) => (Expr::sqrt(Expr::ONE - arg.clone().pow(Expr::from(2))) / *arg).trivial(),
          (EOp::Tan, Expr::Fun(Function::ElemExpr { map: EOp::ArcTan, arg })) => Ok(*arg),

          // [Hyperbolic identities](https://en.wikipedia.org/wiki/Hyperbolic_functions#Useful_relations)
          //
          // Using the equivalent of the Pythagorean identity for hyperbolic geometry:
          // ```sinh(x)^2 - cosh(x)^2 = -1```
          //
          // which can also be solved for either sinh or cosh
          // * ```sinh(x) = +- sqrt(cosh(x)^2 - 1)```
          // * ```cosh(x) = +- sqrt(sinh(x)^2 - 1)```
          //
          // on the unit hyperbola,
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
          //

          // ```sinh(_∞) = arsinh(_∞) = _∞```
          // ```cosh(_∞) = arcosh(_∞) = ∞```
          (EOp::Sinh | EOp::ArSinh, Expr::Cte(Constant::Infinity(z))) => Ok(Expr::Cte(Constant::Infinity(z))),
          (EOp::Cosh | EOp::ArCosh, Expr::Cte(Constant::Infinity(_))) => Ok(Expr::Cte(Constant::Infinity(1))),
          // ```tanh(_∞) = sgn(_∞)```
          // ```artanh(_∞) = -sgn(_∞)*π*I/2```
          (EOp::Tanh, Expr::Cte(Constant::Infinity(z))) => Ok(Expr::from(z)),
          (EOp::ArTanh, Expr::Cte(Constant::Infinity(z))) => (Expr::from(-z) * Expr::Cte(Constant::pi) * Expr::Cte(Constant::I) * Expr::HALF).trivial(),

          // ```sinh(0) = arsinh(0) = 0```
          (EOp::Sinh | EOp::ArSinh, Expr::ZERO) => Ok(Expr::ZERO),
          // ```cosh(0) = 1```
          (EOp::Cosh, Expr::ZERO) => Ok(Expr::ONE),
          // ```tanh(0) = artanh(0) = 0```
          (EOp::Tanh | EOp::ArTanh, Expr::ZERO) => Ok(Expr::ZERO),

          // ```arcosh(0) = π*I/2```
          (EOp::ArCosh, Expr::ZERO) => (Expr::Cte(Constant::pi) * Expr::Cte(Constant::I) * Expr::HALF).trivial(),
          // ```arcosh(1) = 0```
          (EOp::ArCosh, Expr::ONE) => Ok(Expr::ZERO),
          // ```artanh(1) = ∞```
          (EOp::ArTanh, Expr::ONE) => Ok(Expr::Cte(Constant::Infinity(1))),

          // ```sinh(arsinh(x)) = x```
          // ```sinh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)```
          // ```sinh(artanh(x)) = x/sqrt(1 - x^2)```
          (EOp::Sinh, Expr::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => Ok(*arg),
          (EOp::Sinh, Expr::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => (Expr::sqrt(*arg.clone() - Expr::ONE) * Expr::sqrt(*arg + Expr::ONE)).trivial(),
          (EOp::Sinh, Expr::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2)))).trivial(),

          // ```cosh(arsinh(x)) = sqrt(1 + x^2)```
          // ```cosh(arcosh(x)) = x```
          // ```cosh(artanh(x)) = 1/sqrt(1 - x^2)```
          (EOp::Cosh, Expr::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => Expr::sqrt(Expr::ONE + arg.pow(Expr::from(2))).trivial(),
          (EOp::Cosh, Expr::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => Ok(*arg),
          (EOp::Cosh, Expr::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => (Expr::ONE / Expr::sqrt(Expr::ONE - arg.pow(Expr::from(2)))).trivial(),

          // ```tanh(arsinh(x)) = x/(sqrt(1 + x^2))```
          // ```tanh(arcosh(x)) = sqrt(x - 1)*sqrt(x + 1)/x```
          // ```tanh(artanh(x)) = x```
          (EOp::Tanh, Expr::Fun(Function::ElemExpr { map: EOp::ArSinh, arg })) => (*arg.clone() / Expr::sqrt(Expr::ONE + arg.pow(Expr::from(2)))).trivial(),
          (EOp::Tanh, Expr::Fun(Function::ElemExpr { map: EOp::ArCosh, arg })) => (Expr::sqrt(*arg.clone() - Expr::ONE) * Expr::sqrt(*arg.clone() + Expr::ONE) / *arg).trivial(),
          (EOp::Tanh, Expr::Fun(Function::ElemExpr { map: EOp::ArTanh, arg })) => Ok(*arg),

          // [Exponential identities](https://en.wikipedia.org/wiki/Exponential_function)
          //

          // ```log(_∞) = ∞```
          // ```exp(-∞) = 0```
          // ```exp(∞) = ∞```
          (EOp::Log, Expr::Cte(Constant::Infinity(_))) => Ok(Expr::Cte(Constant::Infinity(1))),
          (EOp::Exp, Expr::Cte(Constant::Infinity(-1))) => Ok(Expr::ZERO),
          (EOp::Exp, Expr::Cte(Constant::Infinity(1))) => Ok(Expr::Cte(Constant::Infinity(1))),

          // ```exp(log(x)) = x```
          (EOp::Exp, Expr::Fun(Function::ElemExpr { map: EOp::Log, arg })) => Ok(*arg),

          // ```exp(0) = 1```
          (EOp::Exp, Expr::ZERO) => Ok(Expr::ONE),
          // ```log(0) = -∞```
          (EOp::Log, Expr::ZERO) => Ok(Expr::Cte(Constant::Infinity(-1))),
          // ```log(1) = 0```
          (EOp::Log, Expr::ONE) => Ok(Expr::ZERO),

          // ```log(1/x) = -log(x), x ∈ ℕ```
          (EOp::Log, Expr::Num(rhs)) if rhs.num().eq(&1) => Ok(-Expr::log(Expr::from(rhs.den()))),

          (map, arg) => {
            Ok(arg.elem(map)) //.
          }
        }
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
        write!(f, "{}({})", format!("{:?}", map).to_lowercase(), arg)
      }

      Function::SpecExpr(spe) => match spe {
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
        Special::Fact(arg) => write!(f, "{}!", arg),
      },

      Function::MapExpr {
        //.
        map,
        arg,
      } => {
        let mut iter = arg.iter();
        if let Some(e) = iter.next() {
          let arg = iter.fold(format!("{}", e), |acc, e| acc + &format!(", {}", e));
          write!(
            //.
            f,
            "{}({})",
            map,
            arg
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

impl EOp {
  fn _rewrite(self, _arg: Expr, _o: EOp) -> Expr { todo!() }
}

impl Expr {
  /// ```sin(x)```
  pub fn r#sin(self) -> Self { self.elem(EOp::Sin) }
  /// ```cos(x)```
  pub fn r#cos(self) -> Self { self.elem(EOp::Cos) }
  /// ```tan(x)```
  pub fn r#tan(self) -> Self { self.elem(EOp::Tan) }

  /// ```arcsin(x)```
  pub fn r#arcsin(self) -> Self { self.elem(EOp::ArcSin) }
  /// ```arccos(x)```
  pub fn r#arccos(self) -> Self { self.elem(EOp::ArcCos) }
  /// ```arctan(x)```
  pub fn r#arctan(self) -> Self { self.elem(EOp::ArcTan) }

  /// ```sinh(x)```
  pub fn r#sinh(self) -> Self { self.elem(EOp::Sinh) }
  /// ```cosh(x)```
  pub fn r#cosh(self) -> Self { self.elem(EOp::Cosh) }
  /// ```tanh(x)```
  pub fn r#tanh(self) -> Self { self.elem(EOp::Tanh) }

  /// ```arsinh(x)```
  pub fn r#arsinh(self) -> Self { self.elem(EOp::ArSinh) }
  /// ```arcosh(x)```
  pub fn r#arcosh(self) -> Self { self.elem(EOp::ArCosh) }
  /// ```artanh(x)```
  pub fn r#artanh(self) -> Self { self.elem(EOp::ArTanh) }

  /// ```exp(x)```
  pub fn r#exp(self) -> Self { self.elem(EOp::Exp) }
  /// ```log(x)```
  pub fn r#log(self) -> Self { self.elem(EOp::Log) }

  pub(crate) fn r#elem(self, map: EOp) -> Self { Self::Fun(Function::ElemExpr { map, arg: Box::new(self) }) }

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
}
