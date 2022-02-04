//! Algebraic structures.

mod num_integer;
mod num_rational;

pub mod poly;
pub mod repr;

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul};

pub use num_integer::*;
pub use num_rational::Rational;
pub use repr::*;

/// Type alias for a mathematical resulting form.
pub type SymbolicResult<T> = Result<T, Form>;

/// A countable number (excluding irrational and complex numbers).
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub enum Number {
  /// The ring of integers.
  Z(Integer),
  /// The field of rationals.
  Q(Rational),
}

impl Number {
  /// Return the numerator.
  pub fn num(&self) -> Integer {
    match self {
      Number::Z(
        z, // ```num(z) ∈ ℤ = num(z/1) ∈ ℚ = z,```
      ) => *z,
      Number::Q(
        q, // ```num(n/d) ∈ ℚ = n,```
      ) => q.num(),
    }
  }

  /// Return the denominator.
  pub fn den(&self) -> Integer {
    match self {
      Number::Z(
        _, // ```den(z) ∈ ℤ = den(z/1) ∈ ℚ = 1,```
      ) => 1,
      Number::Q(
        q, // ```den(n/d) ∈ ℚ = d,```
      ) => q.den(),
    }
  }

  /// Determine the special number set.
  pub fn dom(&self) -> Structure {
    if self.den() != 1 {
      Structure::Q
    } else if self.num() < 0 {
      Structure::Z
    } else {
      Structure::N
    }
  }

  /// Return the divisor and remainder.
  pub fn divrem(&self) -> (Integer, Integer) {
    let div = self.num().div_euclid(self.den());
    let rem = self.num().rem_euclid(self.den());
    (div, rem)
  }

  /// Return the inverse (reciprocal).
  pub fn inv(self) -> SymbolicResult<Number> {
    Number::Q(Rational::new(self.den(), self.num())).trivial()
  }

  /// Return the number raised to an integer power.
  pub fn powi(self, n: Integer) -> SymbolicResult<Number> {
    if self.num() != 0 {
      match n.cmp(&0) {
        // ```l^n = 1^(n - 1)*l```
        Ordering::Greater => self.clone().powi(n - 1)?.mul(self),
        // ```l^-n = (1/l)^n```
        Ordering::Less => self.inv()?.powi(-n),
        // ```l^0 = 1```
        Ordering::Equal => Ok(Number::Z(1)),
      }
    } else if n > 0 {
      Ok(Number::Z(0))
    } else {
      Err(
        Form {}, // ```0^-n```
      )
    }
  }

  /// Try to compute the ith root.
  pub fn try_root(self, x: Integer) -> Option<Number> {
    let n = self.den().abs() as u32;
    let m = self.num();

    let mut l = 0i128;
    let mut u = 1i128;
    while u.pow(n) <= x {
      l = u;
      u *= 2;
    }

    loop {
      let step = (u - l) / 2;
      let root = l + step;
      let test = root.pow(n);

      match test.cmp(&x) {
        Ordering::Equal => return Number::Z(root).powi(m).ok(),
        Ordering::Less => l = root,
        Ordering::Greater => u = root,
      }

      if step < 1 {
        return None;
      }
    }
  }

  /// Apply numerical simplifications.
  pub fn trivial(self) -> SymbolicResult<Number> {
    if let Number::Q(q) = self {
      if q.den() == 0 {
        return Err(
          Form {}, // ```n/0```
        );
      }

      let g = Integer::gcd(
        &q.num(), //.
        &q.den(),
      );

      let sgn = q.den().signum();
      let num = q.num() / g * sgn;
      let den = q.den() / g * sgn;

      if den != 1 {
        Ok(Number::Q(Rational::new(num, den)))
      } else {
        Ok(Number::Z(num))
      }
    } else {
      Ok(self)
    }
  }

  // Helpers
  pub(crate) fn helper_len(&self) -> u64 {
    1 + self
      .dom()
      // ℤ -> -
      // ℚ -> /
      .ge(&Structure::Z) as u64
  }
}

impl Add for Number {
  type Output = SymbolicResult<Number>;

  fn add(self, o: Self) -> Self::Output {
    match (self, o) {
      (Number::Z(lhs), Number::Z(rhs)) => Number::Z(lhs + rhs),
      (Number::Q(lhs), Number::Q(rhs)) => Number::Q(lhs + rhs),

      (
        Number::Z(z),
        Number::Q(q),
      )
      | //.
      (
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
        Number::Z(z),
        Number::Q(q),
      )
      | //.
      (
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
      Number::Z(z) => {
        write!(f, "{z}")
      }

      Number::Q(q) => {
        write!(
          f,
          "{}/{}", // fraction
          q.num(),
          q.den()
        )
      }
    }
  }
}

/// An indeterminate form.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub struct Form {}

impl fmt::Display for Form {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "?")
  }
}

/// A list of important mathematical constants.
#[allow(nonstandard_style)]
#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum Constant {
  /// \[_∞] Infinity.
  Infinity(Ordering),

  /// \[i] Imaginary unit.
  i,
  /// \[π] Archimede's constant.
  pi,
  /// \[e] Euler's number.
  e,
}

impl Constant {
  /// Return the associated constant structure.
  pub fn dom(&self) -> Structure {
    match self {
      Constant::Infinity(_) => Structure::AS,

      Constant::i => {
        // i ∈ ℂ
        Structure::C
      }
      Constant::pi => {
        // π ∈ R∖Q
        Structure::R
      }
      Constant::e => {
        // e ∈ R∖Q
        Structure::R
      }
    }
  }

  pub(crate) fn dir_cmp(ord: Ordering) -> Integer {
    ord as Integer
  }

  pub(crate) fn sign_cmp(
    //.
    lhs: Ordering,
    rhs: Ordering,
  ) -> Ordering {
    lhs.cmp(&rhs).min(rhs.cmp(&lhs)).then(Ordering::Greater)
  }
}

impl fmt::Display for Constant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Constant::Infinity(z) => match z {
        // Directed (+)
        Ordering::Greater => write!(f, "oo"),
        // Directed (-)
        Ordering::Less => write!(f, "-oo"),
        // Complex (~)
        Ordering::Equal => write!(f, "~oo"),
      },

      cte => {
        write!(
          f,
          "{cte:?}", // enum notation
        )
      }
    }
  }
}
