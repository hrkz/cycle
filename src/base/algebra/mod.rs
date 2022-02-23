//! Algebraic structures.

mod num_integer;
mod num_natural;
mod num_rational;

pub mod poly;
pub mod repr;

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul};

pub use num_integer::*;
pub use num_natural::*;
pub use num_rational::Rational;
pub use repr::*;

/// Type alias for a mathematical resulting form.
pub type SymbolicResult<T> = Result<T, Form>;

/// A countable number (excluding irrational and complex numbers).
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub enum Number {
  /// The ring of integers.
  Int(Integer),
  /// The field of rationals.
  Rat(Rational),
}

impl Number {
  /// Abstract (unknown) number set.
  pub const AS: NumberSystem = NumberSystem::AS;
  /// The ring of naturals.
  pub const N: NumberSystem = NumberSystem::N;
  /// The ring of integers.
  pub const Z: NumberSystem = NumberSystem::Z;
  /// The field of real numbers.
  pub const R: NumberSystem = NumberSystem::R;
  /// The field of complex numbers.
  pub const C: NumberSystem = NumberSystem::C;

  /// Return the numerator.
  pub fn num(&self) -> &Integer {
    match self {
      Number::Int(
        z, // ```num(z) ∈ ℤ = num(z/1) ∈ ℚ = z,```
      ) => z,
      Number::Rat(
        q, // ```num(n/d) ∈ ℚ = n,```
      ) => &q.num,
    }
  }

  /// Return the denominator.
  pub fn den(&self) -> Integer {
    match self {
      Number::Int(
        _, // ```den(z) ∈ ℤ = den(z/1) ∈ ℚ = 1,```
      ) => Integer::from(1),
      Number::Rat(
        q, // ```den(n/d) ∈ ℚ = d,```
      ) => q.den.clone(),
    }
  }

  /// Determine the number set.
  pub fn dom(&self) -> NumberSystem {
    if self.den() != Integer::ONE {
      NumberSystem::Q
    } else if self.num().is_negative() {
      NumberSystem::Z
    } else {
      NumberSystem::N
    }
  }

  /// Return the inverse (reciprocal).
  pub fn inv(self) -> SymbolicResult<Number> {
    Number::Rat(Rational::new(self.den(), self.num().clone())).trivial()
  }

  /// Raise the number to an integer power.
  pub fn powi(self, n: Integer) -> SymbolicResult<Number> {
    if self.num() != &Integer::ZERO {
      match n.ord() {
        // ```l^n = 1^(n - 1)*l```
        Ordering::Greater => self.clone().powi(n - Integer::from(1))?.mul(self),
        // ```l^-n = (1/l)^n```
        Ordering::Less => self.inv()?.powi(-n),
        // ```l^0 = 1```
        Ordering::Equal => Ok(Number::Int(Integer::from(1))),
      }
    } else if n.is_positive() {
      Ok(Number::Int(Integer::from(0)))
    } else {
      Err(
        Form {}, // ```0^-n```
      )
    }
  }

  /// Try to compute the ith root.
  pub fn try_root(self, x: &Natural) -> Option<Number> {
    if let Ok(n) = u64::try_from(self.den().abs()) {
      let m = self.num();

      let mut l = Natural::from(0u64);
      let mut u = Natural::from(1u64);
      while &u.clone().pow(n) <= x {
        l = u.clone();
        u *= Natural::from(2u64);
      }

      loop {
        let step = (u.clone() - l.clone()) / Natural::from(2u64);
        let root = l.clone() + step.clone();
        let test = root.clone().pow(n);

        match test.cmp(x) {
          Ordering::Equal => return Number::Int(Integer::from(root)).powi(m.clone()).ok(),
          Ordering::Less => l = root,
          Ordering::Greater => u = root,
        }

        if step < Natural::ONE {
          return None;
        }
      }
    } else {
      None
    }
  }

  /// Apply numerical simplifications.
  pub fn trivial(self) -> SymbolicResult<Number> {
    if let Number::Rat(q) = self {
      if q.den == Integer::ZERO {
        return Err(
          Form {}, // ```n/0```
        );
      }

      let g = Integer::gcd(
        q.num.clone(), //.
        q.den.clone(),
      );

      let sgn = q.den.ord() as i64;
      let num = q.num / g.clone() * Integer::from(sgn);
      let den = q.den / g * Integer::from(sgn);

      if den != Integer::ONE {
        Ok(Number::Rat(Rational::new(num, den)))
      } else {
        Ok(Number::Int(num))
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
      .ge(&NumberSystem::Z) as u64
  }
}

impl Add for Number {
  type Output = SymbolicResult<Number>;

  fn add(self, o: Self) -> Self::Output {
    match (self, o) {
      (Number::Int(lhs), Number::Int(rhs)) => Number::Int(lhs + rhs),
      (Number::Rat(lhs), Number::Rat(rhs)) => Number::Rat(lhs + rhs),

      (
        Number::Int(z),
        Number::Rat(q),
      )
      | //.
      (
        Number::Rat(q),
        Number::Int(z),
      ) => {
        Number::Rat(
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
      (Number::Int(lhs), Number::Int(rhs)) => Number::Int(lhs * rhs),
      (Number::Rat(lhs), Number::Rat(rhs)) => Number::Rat(lhs * rhs),

      (
        Number::Int(z),
        Number::Rat(q),
      )
      | //.
      (
        Number::Rat(q),
        Number::Int(z),
      ) => {
        Number::Rat(
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
      Number::Int(z) => {
        write!(f, "{z}")
      }

      Number::Rat(q) => {
        write!(
          f,
          "{}/{}", // fraction
          q.num, q.den
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
  /// Return the associated constant set.
  pub fn dom(&self) -> NumberSystem {
    match self {
      Constant::Infinity(_) => NumberSystem::AS,

      Constant::i => {
        // i ∈ ℂ
        NumberSystem::C
      }
      Constant::pi => {
        // π ∈ R∖Q
        NumberSystem::R
      }
      Constant::e => {
        // e ∈ R∖Q
        NumberSystem::R
      }
    }
  }

  pub(crate) fn sgn(ord: Ordering) -> i64 {
    ord as i64
  }

  pub(crate) fn sgn_cmp(
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

/// A number system.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum NumberSystem {
  /// Abstract (unknown)
  AS,
  /// Natural
  N,
  /// Integer
  Z,
  /// Rational
  Q,
  /// Real
  R,
  /// Complex
  C,
}

impl Theory for NumberSystem {
  fn notation(&self) -> &str {
    match self {
      NumberSystem::AS => "(unknown)",
      // bf N
      NumberSystem::N => "ℕ",
      // bf Z
      NumberSystem::Z => "ℤ",
      // bf Q
      NumberSystem::Q => "ℚ",
      // bf R
      NumberSystem::R => "ℝ",
      // bf C
      NumberSystem::C => "ℂ",
    }
  }
}
