mod num_integer;
mod num_rational;
mod poly;
mod repr;

use std::cmp::Ordering;
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
  pub fn num(&self) -> Integer {
    match self {
      // ```num(z) ∈ ℤ = num(z/1) ∈ ℚ = z,```
      Number::Z(z) => {
        z.num() //.
      }

      // ```num(n/d) ∈ ℚ = n,```
      Number::Q(q) => {
        q.num() //.
      }
    }
  }

  pub fn den(&self) -> Integer {
    match self {
      // ```den(z) ∈ ℤ = den(z/1) ∈ ℚ = 1,```
      Number::Z(z) => {
        z.den() //.
      }

      // ```den(n/d) ∈ ℚ = d,```
      Number::Q(q) => {
        q.den() //.
      }
    }
  }

  pub fn len(&self) -> u64 { 1 + (self.den() != 1 || self.num().is_negative()) as u64 }

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

  pub fn divmod(&self) -> (Integer, Integer) { (self.num().div_euclid(self.den()), self.num().rem_euclid(self.den())) }

  pub fn inv(self) -> SymbolicResult<Number> { Number::Q(Rational::new(self.den(), self.num())).trivial() }

  pub fn powi(self, n: Integer) -> SymbolicResult<Number> {
    if self.num() != 0 {
      if n > 0 {
        // ```l^n = 1^(n - 1)*l```
        self.clone().powi(n - 1)?.mul(self)
      } else if n < 0 {
        // ```l^-n = (1/l)^n```
        self.inv()?.powi(-n)
      } else {
        Ok(Number::Z(1))
      }
    } else {
      if n > 0 {
        Ok(Number::Z(0))
      } else {
        Err(Form {})
      }
    }
  }

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

  pub fn trivial(self) -> SymbolicResult<Number> {
    match self {
      Number::Q(q) => {
        if q.den() == 0 {
          return Err(Form {});
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
      }

      _ => {
        Ok(self) //.
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
      Number::Z(z) => write!(f, "{}", z),

      Number::Q(q) => {
        write!(
          //.
          f,
          "{}/{}",
          q.num(),
          q.den()
        )
      }
    }
  }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
/// Mathematical error
pub struct Form {}

impl fmt::Display for Form {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "?") }
}

#[allow(nonstandard_style)]
#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
/// Special constants
pub enum Constant {
  /// \[_∞] Infinity
  Infinity(Integer),

  /// \[π] pi, Archimede's constant
  pi,
  /// \[φ] Golden ratio
  GoldenRatio,
  /// \[G] Catalan's constant
  Catalan,
  /// \[γ] Euler-Mascheroni constant
  Euler,
  /// \[K] Khinchin's constant
  Khinchin,
  /// \[A] Glaisher's constant
  Glaisher,
  /// \[ζ3] Apéry's constant
  Apery,

  /// \[i] Imaginary number
  I,
}

impl fmt::Display for Constant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Constant::Infinity(z) => match z {
        // Directed (+)
        z if z.is_positive() => write!(f, "oo"),
        // Directed (-)
        z if z.is_negative() => write!(f, "-oo"),
        // Complex (~)
        _ => write!(f, "~oo"),
      },

      cte => {
        write!(
          //.
          f,
          "{:?}",
          cte
        )
      }
    }
  }
}
