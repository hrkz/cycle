use std::fmt;

use crate::{Constant, Expr, Form, Number, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub enum ElemOp {
  // Cartesian (circular, hyperbolic)
  Cart(CartExpr),

  // Exponential
  Exp,
  Log,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub struct CartExpr {
  map: CartOp,
  fig: FigOp,
  ord: bool,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub enum CartOp {
  Sin,
  Cos,
  Tan,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Copy)]
pub enum FigOp {
  Cir,
  Hyp,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Special {
  /// ```(f ∘ g)(x)```
  Comp(Box<Expr>, Box<Expr>),
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
        let arg = arg.trivial()?;

        match map {
          ElemOp::Cart(CartExpr {
            //.
            map,
            fig,
            ord,
          }) => {
            match (arg, map, fig, ord) {
              (Expr::Cte(Constant::Infinity(0)), _, _, _) => Err(Form {}),

              // ```sin(0) = sinh(0) = 0```
              (Expr::ZERO, CartOp::Sin, _, true) => Ok(Expr::ZERO),
              // ```cos(0) = cosh(0) = 1```
              (Expr::ZERO, CartOp::Cos, _, true) => Ok(Expr::ONE),
              // ```tan(0) = tanh(0) = 0```
              (Expr::ZERO, CartOp::Tan, _, true) => Ok(Expr::ZERO),

              // ```arcsin(0) = 0```
              (Expr::ZERO, CartOp::Sin, FigOp::Cir, false) => Ok(Expr::ZERO),
              // ```arccos(0) = π/2```
              (Expr::ZERO, CartOp::Cos, FigOp::Cir, false) => (Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
              // ```arctan(0) = 0```
              (Expr::ZERO, CartOp::Tan, FigOp::Cir, false) => Ok(Expr::ZERO),

              // ```arcsin(1) = π/2```
              (Expr::ONE, CartOp::Sin, FigOp::Cir, false) => (Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
              // ```arccos(1) = 0```
              (Expr::ONE, CartOp::Cos, FigOp::Cir, false) => Ok(Expr::ZERO),
              // ```arctan(1) = π/4```
              (Expr::ONE, CartOp::Tan, FigOp::Cir, false) => (Expr::Cte(Constant::pi) * Expr::QUARTER).trivial(),

              // ```ar{}(0)h = arc{}(0)*I```
              (Expr::ZERO, map, FigOp::Hyp, false) => (Expr::ZERO.cart(map, FigOp::Cir, false) * Expr::Cte(Constant::I)).trivial(),

              // ```arctan(_∞) = sgn(_)*π/2```
              (Expr::Cte(Constant::Infinity(z)), CartOp::Tan, FigOp::Cir, false) => (Expr::Num(Number::Z(z)) * Expr::Cte(Constant::pi) * Expr::HALF).trivial(),
              // ```actanh(_∞) = -sgn(_)*π*I/2```
              (Expr::Cte(Constant::Infinity(z)), CartOp::Tan, FigOp::Hyp, false) => (-Expr::Num(Number::Z(z)) * Expr::Cte(Constant::pi) * Expr::Cte(Constant::I) * Expr::HALF).trivial(),
              // ```tanh(_∞) = sgn(_)```
              (Expr::Cte(Constant::Infinity(z)), CartOp::Tan, FigOp::Hyp, true) => Ok(Expr::Num(Number::Z(z))),
              // ```cosh(_∞) = sinh(_∞) = arcosh(_∞) = arsinh(_∞) = _∞```
              (Expr::Cte(Constant::Infinity(z)), _, FigOp::Hyp, _) => Ok(Expr::Cte(Constant::Infinity(z))),

              // ```cart{}(cart{}^-1(x))```
              (Expr::Fun(Function::ElemExpr { map: ElemOp::Cart(comp), arg }), map, fig, true) if !comp.ord && comp.fig == fig => map.composition(comp.map, fig, *arg),

              // π and I reflections
              (arg, map, fig, ord) => {
                Ok(arg.cart(map, fig, ord)) //.
              }
            }
          }

          ElemOp::Exp => match arg {
            // ```exp(0) = 1```
            Expr::ZERO => Ok(Expr::ONE),
            // ```exp(-∞) = 0```
            Expr::Cte(Constant::Infinity(-1)) => Ok(Expr::ZERO),
            // ```exp(∞) = ∞```
            Expr::Cte(Constant::Infinity(1)) => Ok(Expr::Cte(Constant::Infinity(1))),

            // ```exp(log(x)) = x```
            Expr::Fun(Function::ElemExpr {
              //.
              map: ElemOp::Log,
              arg,
            }) => {
              Ok(*arg) //.
            }

            // exp π*I reflections
            arg => {
              Ok(arg.exp()) //.
            }
          },

          ElemOp::Log => match arg {
            // ```log(1) = 0```
            Expr::ONE => Ok(Expr::ZERO),
            // ```log(_∞) = ∞```
            Expr::Cte(Constant::Infinity(_)) => Ok(Expr::Cte(Constant::Infinity(1))),

            // ```log(exp(x)) = x```
            Expr::Fun(Function::ElemExpr {
              //.
              map: ElemOp::Exp,
              arg,
            }) => {
              Ok(*arg) //.
            }

            // log sign
            // log I reflections
            arg => {
              Ok(arg.log()) //.
            }
          },
        }
      }

      _ => {
        Ok(Expr::Fun(self)) //.
      }
    }
  }

  pub fn subs(&self, m: &Expr, s: &Expr) -> Expr {
    match self {
      Function::ElemExpr {
        //.
        map,
        arg,
      } => Expr::Fun(Function::ElemExpr {
        map: *map,
        arg: Box::new(arg.subs(m, s)),
      }),

      Function::SpecExpr(
        //.
        map,
      ) => match map {
        Special::Comp(lhs, rhs) => Expr::Fun(Function::SpecExpr(Special::Comp(Box::new(lhs.subs(m, s)), Box::new(rhs.subs(m, s))))),
      },

      Function::MapExpr {
        //.
        map,
        arg,
      } => Expr::Fun(Function::MapExpr {
        map: map.clone(),
        arg: arg.iter().map(|x| x.subs(m, s)).collect(),
      }),
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
          format!("{}", map).to_lowercase(),
          arg
        )
      }

      Function::SpecExpr(
        //.
        map,
      ) => {
        //.
        match map {
          Special::Comp(lhs, rhs) => write!(f, "{} ∘ {}", lhs, rhs),
        }
      }

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
            "{}",
            map
          )
        }
      }
    }
  }
}

impl CartOp {
  fn composition(
    //.
    self,
    map: CartOp,
    fig: FigOp,
    arg: Expr,
  ) -> SymbolicResult<Expr> {
    if self.eq(&map) {
      Ok(arg) //.
    } else {
      let tr_a = Expr::ONE;
      let tr_b = arg.clone();
      let tr_c = arg.pow(Expr::Num(Number::Z(2)));

      match (fig, map) {
        // ```cos(arcsin(x)) = sqrt(1 - x^2)```
        // ```tan(arcsin(x)) = x/(sqrt(1 - x^2))```
        (FigOp::Cir, CartOp::Sin) => self.triangle(tr_a.clone(), tr_b, (tr_a - tr_c).sqrt()),
        // ```sin(arccos(x)) = sqrt(1 - x^2)```
        // ```tan(arccos(x)) = sqrt(1 - x^2)/x```
        (FigOp::Cir, CartOp::Cos) => self.triangle(tr_a.clone(), (tr_a - tr_c).sqrt(), tr_b),
        // ```sin(arctan(x)) = x/sqrt(1 + x^2)```
        // ```cos(arctan(x)) = 1/sqrt(1 + x^2)```
        (FigOp::Cir, CartOp::Tan) => self.triangle((tr_a.clone() + tr_c).sqrt(), tr_b, tr_a),
        // ```cosh(arsinh(x)) = sqrt(1 + x^2)```
        // ```tanh(arsinh(x)) = x/sqrt(1 + x^2)```
        (FigOp::Hyp, CartOp::Sin) => self.triangle(tr_a.clone(), tr_b, (tr_a + tr_c).sqrt()),
        // ```sinh(arcosh(x)) = sqrt(x^2 - 1)```
        // ```tanh(arcosh(x)) = sqrt(x^2 - 1)/x```
        (FigOp::Hyp, CartOp::Cos) => self.triangle(tr_a.clone(), (tr_c - tr_a).sqrt(), tr_b),
        // ```sinh(artanh(x)) = x/sqrt(1 - x^2)```
        // ```cosh(artanh(x)) = 1/sqrt(1 - x^2)```
        (FigOp::Hyp, CartOp::Tan) => self.triangle((tr_a.clone() - tr_c).sqrt(), tr_b, tr_a),
      }
      .trivial()
    }
  }

  fn triangle(
    //.
    self,
    hypot: Expr,
    opp: Expr,
    adj: Expr,
  ) -> Expr {
    match self {
      CartOp::Sin => opp / hypot,
      CartOp::Cos => adj / hypot,
      CartOp::Tan => opp / adj,
    }
  }
}

impl fmt::Display for ElemOp {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      ElemOp::Cart(CartExpr {
        //.
        map,
        fig,
        ord,
      }) => match (fig, ord) {
        (FigOp::Cir, true) => write!(f, "{:?}", map),
        (FigOp::Hyp, true) => write!(f, "{:?}h", map),
        (FigOp::Cir, false) => write!(f, "Arc{:?}", map),
        (FigOp::Hyp, false) => write!(f, "Ar{:?}h", map),
      },

      map => {
        write!(
          //.
          f,
          "{:?}",
          map
        )
      }
    }
  }
}

impl Expr {
  /// ```sin(x)```
  pub fn r#sin(self) -> Self { self.cart(CartOp::Sin, FigOp::Cir, true) }
  /// ```cos(x)```
  pub fn r#cos(self) -> Self { self.cart(CartOp::Cos, FigOp::Cir, true) }
  /// ```tan(x)```
  pub fn r#tan(self) -> Self { self.cart(CartOp::Tan, FigOp::Cir, true) }

  /// ```arcsin(x)```
  pub fn r#arcsin(self) -> Self { self.cart(CartOp::Sin, FigOp::Cir, false) }
  /// ```arccos(x)```
  pub fn r#arccos(self) -> Self { self.cart(CartOp::Cos, FigOp::Cir, false) }
  /// ```arctan(x)```
  pub fn r#arctan(self) -> Self { self.cart(CartOp::Tan, FigOp::Cir, false) }

  /// ```sinh(x)```
  pub fn r#sinh(self) -> Self { self.cart(CartOp::Sin, FigOp::Hyp, true) }
  /// ```cosh(x)```
  pub fn r#cosh(self) -> Self { self.cart(CartOp::Cos, FigOp::Hyp, true) }
  /// ```tanh(x)```
  pub fn r#tanh(self) -> Self { self.cart(CartOp::Tan, FigOp::Hyp, true) }

  /// ```arsinh(x)```
  pub fn r#arsinh(self) -> Self { self.cart(CartOp::Sin, FigOp::Hyp, false) }
  /// ```arcosh(x)```
  pub fn r#arcosh(self) -> Self { self.cart(CartOp::Cos, FigOp::Hyp, false) }
  /// ```artanh(x)```
  pub fn r#artanh(self) -> Self { self.cart(CartOp::Tan, FigOp::Hyp, false) }

  /// ```exp(x)```
  pub fn r#exp(self) -> Self { self.elem(ElemOp::Exp) }
  /// ```log(x)```
  pub fn r#log(self) -> Self { self.elem(ElemOp::Log) }

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

  fn r#cart(self, map: CartOp, fig: FigOp, ord: bool) -> Self { self.elem(ElemOp::Cart(CartExpr { map, fig, ord })) }

  fn r#elem(self, map: ElemOp) -> Self {
    Self::Fun(Function::ElemExpr {
      //.
      map,
      arg: Box::new(self),
    })
  }
}
