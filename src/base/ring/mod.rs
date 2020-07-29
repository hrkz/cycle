pub mod num_complex;
pub mod num_integer;
pub mod num_rational;

use std::fmt;
use std::ops::{Add, Mul};

pub use num_integer::*;
pub use num_rational::Rational;

pub type SymbolicResult<T> = Result<T, Form>;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub enum Number {
  Z(i64),
  Q(Rational),
}

impl Number {
  pub const ZERO: Number = Number::Z(0);
  pub const ONE: Number = Number::Z(1);
  pub const NEG_ONE: Number = Number::Z(-1);

  pub fn num(&self) -> i64 {
    match self {
      // num(z) \in \mathbb{Z} = num(z/1) \in \mathbb{Q} = z,
      Number::Z(z) => {
        *z //.
      }

      // num(n/d) \in \mathbb{Q} = n,
      Number::Q(q) => {
        q.num //.
      } /*
        Number::T(_) => {
          None
        }
        */
    }
  }

  pub fn den(&self) -> i64 {
    match self {
      // den(z) \in \mathbb{Z} = den(z/1) \in \mathbb{Q} = 1,
      Number::Z(_) => {
        1 //.
      }

      // den(n/d) \in \mathbb{Q} = d,
      Number::Q(q) => {
        q.den //.
      } /*
        Number::T(_) => {
          1
        }
        */
    }
  }

  pub fn len(&self) -> u64 { 1 + (self.den() > 1) as u64 }
  pub fn ord(&self) -> u64 { self.len() }

  pub fn inv(self) -> SymbolicResult<Number> { Number::Q(Rational::new(self.den(), self.num())).trivial() }

  pub fn pow(self, n: i64) -> SymbolicResult<Number> {
    if self.num() != 0 {
      if n > 0 {
        // l^n = 1^(n - 1)*l
        self.clone().pow(n - 1)?.mul(self)
      } else if n < 0 {
        // l^-n = (1/l)^n
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
        if q.den == 0 {
          if q.num == 0 {
            return Err(Form::Indeterminate);
          } else {
            return Err(Form::ComplexInf);
          }
        }

        let g = gcd(q.num, q.den);

        let num = q.num / g * q.den.signum();
        let den = q.den / g * q.den.signum();

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

  /// ```a/b + c/d = (a*lcm/b + c*lcm/d)/lcm where lcm = lcm(b,d)```
  fn add(self, o: Self) -> Self::Output {
    let (ln, rn) = (self.num(), o.num());
    let (ld, rd) = (self.den(), o.den());

    let lcm = gcd_lcm(ld, rd).1;
    let lhs_num = ln * lcm / ld;
    let rhs_num = rn * lcm / rd;

    Number::Q(Rational::new(lhs_num + rhs_num, lcm)).trivial()
  }
}

impl Mul for Number {
  type Output = SymbolicResult<Number>;

  /// ```a/b * c/d = (a/gcd_ad)*(c/gcd_bc) / ((d/gcd_ad)*(b/gcd_bc))```
  fn mul(self, o: Self) -> Self::Output {
    let (ln, rn) = (self.num(), o.num());
    let (ld, rd) = (self.den(), o.den());

    let gcd_ad = gcd(ln, rd);
    let gcd_bc = gcd(ld, rn);

    Number::Q(Rational::new(ln / gcd_ad * rn / gcd_bc, rd / gcd_ad * ld / gcd_bc)).trivial()
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
          //. signs
          q.num,
          q.den
        )
      }
    }
  }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq)]
pub enum Ring {
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

#[derive(Debug, Clone, PartialEq)]
pub enum Form {
  /// Infinity on complex manifold i.e. Riemann sphere
  ComplexInf,

  /// Also represents mathematical error
  Indeterminate,
  //.
}

#[derive(Debug, Clone, PartialEq)]
/// Special constants
#[allow(non_camel_case_types)]
pub enum Constant {
  /// Infinity
  oo,
  /// Imaginary number
  im,

  /// Pi, Archimede's constant
  pi,
  /// Euler's number
  e,
}

impl fmt::Display for Constant {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      // special values
      Constant::oo => write!(f, "∞"),
      Constant::im => write!(f, "i"),

      // constants
      Constant::pi => {
        //.
        write!(f, "π")
      }
      Constant::e => {
        //.
        write!(f, "e")
      }
    }
  }
}
