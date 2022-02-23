use crate::base::algebra::num_natural::*;
use crate::base::algebra::repr::*;
use Sign::*;

use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign};
use std::str::FromStr;

/// An integer ℤ.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub struct Integer {
  pub(crate) sgn: Sign,
  pub(crate) mag: Natural,
}

impl Integer {
  /// The additive identity 0.
  pub const ZERO: Integer = Integer { sgn: Positive, mag: Natural::ZERO };
  /// The multiplicative identity 1.
  pub const ONE: Integer = Integer { sgn: Positive, mag: Natural::ONE };
  /// The multiplicative double 2.
  pub const TWO: Integer = Integer { sgn: Positive, mag: Natural::TWO };
  /// The negative identity -1.
  pub const NEG_ONE: Integer = Integer { sgn: Negative, mag: Natural::ONE };

  pub(crate) const fn from_sgn(
    sgn: Sign, //.
    mag: Natural,
  ) -> Self {
    Integer {
      sgn, //.
      mag,
    }
  }

  pub(crate) fn incr(&mut self) {
    *self = mem::take(self) + Self::ONE;
  }

  /// Return `true` if `self` is positive and `false` if the number is zero or negative.
  pub const fn is_positive(&self) -> bool {
    matches!(self.sgn, Positive) && !matches!(self.mag, Natural::ZERO)
  }
  /// Return `true` if `self` is negative and `false` if the number is zero or positive.
  pub const fn is_negative(&self) -> bool {
    matches!(self.sgn, Negative) && !matches!(self.mag, Natural::ZERO)
  }

  /// Return an ordering representing the sign of `self`.
  pub fn ord(&self) -> Ordering {
    self.cmp(&Integer::ZERO)
  }

  /// Compute the absolute value of `self`.
  pub fn abs(self) -> Natural {
    self.mag
  }

  /// Raise `self` to the power of `exp`.
  pub fn pow(self, exp: u64) -> Self {
    let sgn = if self.sgn == Negative && exp % 2 == 1 { Negative } else { Positive };
    Integer::from_sgn(sgn, self.mag.pow(exp))
  }

  /// Compute the Greatest Common Divisor (GCD) of two integers `u` and `v`.
  pub fn gcd(u: Self, v: Self) -> Self {
    Integer::from(Natural::gcd(u.abs(), v.abs()))
  }

  /// Compute the Lowest Common Multiple (LCM) of two integers `u` and `v`.
  pub fn lcm(u: Self, v: Self) -> Self {
    Integer::from(Natural::lcm(u.abs(), v.abs()))
  }
}

impl Neg for Integer {
  type Output = Integer;

  #[inline]
  fn neg(self) -> Self::Output {
    Integer { sgn: self.sgn.neg(), mag: self.mag }
  }
}

impl Add for Integer {
  type Output = Integer;

  #[inline]
  fn add(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    match (self.sgn, rhs.sgn) {
      (Positive, Positive) => Integer::from(self.mag + rhs.mag),
      (Negative, Negative) => -Integer::from(self.mag + rhs.mag),
      (Positive, Negative) => Integer::from(Sign::diff(
        self.mag.0, // lhs + (-rhs)
        rhs.mag.0,
      )),
      (Negative, Positive) => Integer::from(Sign::diff(
        rhs.mag.0, // rhs + (-lhs)
        self.mag.0,
      )),
    }
  }
}

impl AddAssign for Integer {
  #[inline]
  fn add_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) + rhs;
  }
}

impl Sub for Integer {
  type Output = Integer;

  #[inline]
  fn sub(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    self + -rhs
  }
}

impl SubAssign for Integer {
  #[inline]
  fn sub_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) - rhs;
  }
}

impl Mul for Integer {
  type Output = Integer;

  #[inline]
  fn mul(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Integer {
      sgn: self.sgn * rhs.sgn,
      mag: self.mag * rhs.mag,
    }
  }
}

impl MulAssign for Integer {
  #[inline]
  fn mul_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) * rhs;
  }
}

impl Div for Integer {
  type Output = Integer;

  #[inline]
  fn div(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Integer {
      sgn: self.sgn * rhs.sgn,
      mag: self.mag / rhs.mag,
    }
  }
}

impl DivAssign for Integer {
  #[inline]
  fn div_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) / rhs;
  }
}

impl Rem for Integer {
  type Output = Integer;

  #[inline]
  fn rem(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Integer {
      sgn: self.sgn,
      mag: self.mag % rhs.mag,
    }
  }
}

impl RemAssign for Integer {
  #[inline]
  fn rem_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) % rhs;
  }
}

impl Integer {
  /// Compute the divisor and remainder of two integers.
  pub fn div_rem(self, o: Self) -> (Self, Self) {
    let (q, r) = self.mag.div_rem(o.mag);
    (Integer::from_sgn(self.sgn * o.sgn, q), Integer::from_sgn(self.sgn, r))
  }

  /// Compute the quotient of Euclidean division of `self` by `o`.
  pub fn div_euclid(self, o: Self) -> Self {
    let s = o.ord();
    let (q, r) = self.div_rem(o);
    match r.sgn {
      Positive => q,
      Negative => q - Integer::from(s as i64),
    }
  }

  /// Compute the least nonnegative remainder of `self` (mod `o`).
  pub fn rem_euclid(self, o: Self) -> Self {
    let s = o.clone().abs();
    let r = self % o;
    match r.sgn {
      Positive => r,
      Negative => r + Integer::from(s),
    }
  }
}

impl FromStr for Integer {
  type Err = ParseError;

  fn from_str(s: &str) -> Result<Integer, ParseError> {
    let (sgn, num) = s.strip_prefix('-').map(|num| (Negative, num)).unwrap_or((Positive, s));
    let mag = Natural::from_str(num)?;
    Ok(Integer {
      sgn, //.
      mag,
    })
  }
}

impl From<(Sign, Digits)> for Integer {
  fn from((sgn, dgt): (Sign, Digits)) -> Integer {
    Integer::from_sgn(sgn, Natural(dgt))
  }
}

impl From<u32> for Integer {
  /// Produce a positive integer from a [`u32`].
  fn from(n: u32) -> Integer {
    Integer::from((Positive, Digits::from(n as u64)))
  }
}

impl From<i32> for Integer {
  /// Produce an integer from a [`i32`].
  fn from(i: i32) -> Self {
    Integer::from((Sign::from(i.signum() as i32), Digits::from(i.unsigned_abs() as u64)))
  }
}

impl From<u64> for Integer {
  /// Produce a positive integer from a [`u64`].
  fn from(n: u64) -> Integer {
    Integer::from((Positive, Digits::from(n as u64)))
  }
}

impl From<i64> for Integer {
  /// Produce an integer from a [`i64`].
  fn from(i: i64) -> Integer {
    Integer::from((Sign::from(i.signum() as i32), Digits::from(i.unsigned_abs() as u64)))
  }
}

impl From<Natural> for Integer {
  /// Produce a positive integer from a [`Natural`].
  fn from(mag: Natural) -> Integer {
    Integer { sgn: Positive, mag }
  }
}

impl TryFrom<Integer> for Natural {
  type Error = ();

  fn try_from(z: Integer) -> Result<Self, Self::Error> {
    if z.sgn != Sign::Negative {
      Ok(z.mag)
    } else {
      Err(
        (), //.
      )
    }
  }
}

impl Default for Integer {
  /// The identity integer 0 (zero).
  fn default() -> Self {
    Integer::ZERO
  }
}

impl fmt::Display for Integer {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.pad_integral(matches!(self.sgn, Positive), "ℤ", &format!("{}", self.mag))
  }
}
