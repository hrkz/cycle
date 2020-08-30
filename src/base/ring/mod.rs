mod num_integer;
mod num_rational;
mod poly;
mod repr;

use std::fmt;
use std::ops::{Add, Mul};

pub use num_integer::*;
pub use num_rational::Rational;
pub use repr::*;

pub type SymbolicResult<T> = Result<T, Form>;

#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub enum Number {
  Z(Integer),
  Q(Rational),
}

impl Number {
  pub const ZERO: Number = Number::Z(0);
  pub const ONE: Number = Number::Z(1);
  pub const NEG_ONE: Number = Number::Z(-1);

  pub fn num(&self) -> i128 {
    match self {
      // ```num(z) \in \mathbb{Z} = num(z/1) \in \mathbb{Q} = z,```
      Number::Z(z) => {
        z.num() //.
      }

      // ```num(n/d) \in \mathbb{Q} = n,```
      Number::Q(q) => {
        q.num() //.
      }
    }
  }

  pub fn den(&self) -> i128 {
    match self {
      // ```den(z) \in \mathbb{Z} = den(z/1) \in \mathbb{Q} = 1,```
      Number::Z(z) => {
        z.den() //.
      }

      // ```den(n/d) \in \mathbb{Q} = d,```
      Number::Q(q) => {
        q.den() //.
      }
    }
  }

  pub fn ord(&self) -> u64 { self.len() }
  pub fn len(&self) -> u64 { 1 + (self.den() != 1) as u64 }

  pub fn dom(&self) -> Set {
    if self.den() != 1 {
      Set::Q
    } else {
      if self.num() < 0 {
        Set::Z
      } else {
        Set::N
      }
    }
  }

  pub fn inv(self) -> SymbolicResult<Number> { Number::Q(Rational::new(self.den(), self.num())).trivial() }

  pub fn pow(self, n: i128) -> SymbolicResult<Number> {
    if self.num() != 0 {
      if n > 0 {
        // ```l^n = 1^(n - 1)*l```
        self.clone().pow(n - 1)?.mul(self)
      } else if n < 0 {
        // ```l^-n = (1/l)^n```
        self.inv()?.pow(-n)
      } else {
        Ok(Number::Z(1))
      }
    } else {
      if n < 0 {
        Err(Form::ComplexInf)
      } else if n == 0 {
        Ok(Number::Z(1))
      } else {
        Ok(Number::Z(0))
      }
    }
  }

  pub fn trivial(self) -> SymbolicResult<Number> {
    match self {
      Number::Q(q) => {
        if q.den() == 0 {
          if q.num() == 0 {
            return Err(Form::Indeterminate);
          } else {
            return Err(Form::ComplexInf);
          }
        }

        let g = Integer::gcd(&q.num(), &q.den());

        let num = q.num() / g * q.den().signum();
        let den = q.den() / g * q.den().signum();

        if den != 1 {
          Ok(Number::Q(Rational::new(num, den)))
        } else {
          Ok(Number::Z(num))
        }
      }

      _ => {
        //.
        Ok(self)
      }
    }
  }
}

impl Add for Number {
  type Output = SymbolicResult<Number>;

  fn add(self, o: Self) -> Self::Output {
    match (self, o) {
      (Number::Z(lhs), Number::Z(rhs)) => Number::Z(lhs + rhs),
      (Number::Q(lhs), Number::Q(rhs)) => Number::Q(lhs + rhs),

      (
        //.
        Number::Z(z),
        Number::Q(q),
      )
      | (
        //.
        Number::Q(q),
        Number::Z(z),
      ) => {
        Number::Q(
          // ```a/b + c/1 = (a + c)/b```
          q + Rational::from(z),
        )
      }
    }
    .trivial()
  }
}

impl Mul for Number {
  type Output = SymbolicResult<Number>;

  fn mul(self, o: Self) -> Self::Output {
    match (self, o) {
      (Number::Z(lhs), Number::Z(rhs)) => Number::Z(lhs * rhs),
      (Number::Q(lhs), Number::Q(rhs)) => Number::Q(lhs * rhs),

      (
        //.
        Number::Z(z),
        Number::Q(q),
      )
      | (
        //.
        Number::Q(q),
        Number::Z(z),
      ) => {
        Number::Q(
          // ```a/b * c/1 = a*b/c```
          q * Rational::from(z),
        )
      }
    }
    .trivial()
  }
}

impl fmt::Display for Number {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Number::Z(z) => write!(f, "{}", z),

      Number::Q(q) => {
        write!(
          f,
          "{}/{}",
          // signs
          q.num(),
          q.den()
        )
      }
    }
  }
}

#[derive(Debug, Clone, Hash, PartialEq)]
pub enum Form {
  /// Infinity on complex manifold i.e. Riemann sphere
  ComplexInf,

  /// Also represents mathematical error
  Indeterminate,
  //.
}

#[derive(Debug, Clone, Hash, PartialEq)]
/// Special constants
pub enum Constant {
  /// Infinity
  Infinity,

  /// Pi, Archimede's constant
  Pi,
  /// Euler's number
  Euler,
  /// Golden ratio
  Golden,
  /// Catalan's constant
  Catalan,
  /// Conway's constant
  Conway,

  /// Imaginary number
  I,
}

impl fmt::Display for Constant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      // special values
      Constant::Infinity => write!(f, "∞"),

      // constants
      Constant::Pi => {
        write!(f, "[π]") //.
      }
      Constant::Euler => {
        write!(f, "[e]") //.
      }
      Constant::Golden => {
        write!(f, "[φ]") //.
      }
      Constant::Catalan => {
        write!(f, "[G]") //.
      }
      Constant::Conway => {
        write!(f, "[λ]") //.
      }

      Constant::I => {
        write!(f, "[I]") //.
      }
    }
  }
}
