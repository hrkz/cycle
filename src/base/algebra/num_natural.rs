use crate::base::algebra::repr::*;

use std::cmp;
use std::fmt;
use std::mem;
use std::ops::{Add, AddAssign, BitOr, BitOrAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::str::FromStr;

/// A natural ℕ.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord)]
pub struct Natural(pub(crate) Digits);

impl Natural {
  /// The additive identity 0.
  pub const ZERO: Natural = Natural(Digits::Fix(0));
  /// The multiplicative identity 1.
  pub const ONE: Natural = Natural(Digits::Fix(1));
  /// The multiplicative double 2.
  pub const TWO: Natural = Natural(Digits::Fix(2));

  pub(crate) fn incr(&mut self) {
    *self = mem::take(self) + Self::ONE;
  }

  pub(crate) fn decr(&mut self) {
    *self = mem::take(self) - Self::ONE;
  }

  /// Return true if and only if `self = 2^k` for some `k`.
  pub fn is_power_of_two(&self) -> bool {
    self.0.is_power_of_two()
  }

  /// Return the number of leading zeros in the binary representation of `self`.
  pub fn leading_zeros(&self) -> usize {
    self.0.leading_zeros()
  }

  /// Return the number of trailing zeros in the binary representation of `self`.
  pub fn trailing_zeros(&self) -> usize {
    self.0.trailing_zeros()
  }

  /// Raise `self` to the power of `exp`.
  pub fn pow(self, exp: u64) -> Self {
    let mut bit = u64::BITS - 2 - exp.leading_zeros();
    let mut pow = self.clone() * self.clone();

    loop {
      if exp & (1 << bit) != 0 {
        pow *= self.clone();
      }
      if bit == 0 {
        break;
      }
      bit -= 1;
      pow *= pow.clone();
    }
    pow
  }

  /// Compute the divisor and remainder of two naturals.
  pub fn div_rem(self, o: Self) -> (Self, Self) {
    let (q, r) = self.0.div_rem(o.0);
    (Natural(q), Natural(r))
  }

  /// Compute the Greatest Common Divisor (GCD) of two naturals `u` and `v`.
  pub fn gcd(u: Self, v: Self) -> Self {
    match (u, v) {
      // ```gcd(u, 0) = u```
      (u, Self::ZERO) => u,
      // ```gcd(0, v) = v```
      (Self::ZERO, v) => v,

      (mut u, mut v) => {
        let i = u.trailing_zeros();
        let j = v.trailing_zeros();
        u >>= i;
        v >>= j;

        while v != Self::ZERO {
          v >>= v.trailing_zeros();

          if u > v {
            mem::swap(&mut u, &mut v); // u <= v
          }
          v -= u.clone();
        }

        u << cmp::min(
          i, // restore
          j,
        )
      }
    }
  }

  /// Compute the Lowest Common Multiple (LCM) of two naturals `u` and `v`.
  pub fn lcm(u: Self, v: Self) -> Self {
    match (u, v) {
      (Self::ZERO, Self::ZERO) => {
        // ```gcd(0, 0) = 0```
        // ```lcm(0, 0) = 0 otherwise undefined```
        Self::ZERO
      }

      (u, v) => {
        let gcd = Self::gcd(u.clone(), v.clone());
        (u * v) / gcd
      }
    }
  }

  /// Compute the factorial `n!`.
  pub fn factorial(n: Self) -> Self {
    let mut f = Self::ONE;
    let mut i = Self::ONE;

    while i <= n {
      f *= i.clone();
      i.incr();
    }
    f
  }

  /// Compute the binomial coefficient `(n k)`.
  pub fn binomial(mut n: Self, k: Self) -> Self {
    if k > n {
      return Self::ZERO;
    }
    if k > (n.clone() - k.clone()) {
      return Self::binomial(n.clone(), n - k);
    }

    let mut b = Self::ONE;
    let mut i = Self::ONE;

    while i <= k {
      b *= n.clone();
      b /= i.clone();
      n.decr();
      i.incr();
    }
    b
  }
}

impl Add for Natural {
  type Output = Natural;

  #[inline]
  fn add(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Natural(self.0 + rhs.0)
  }
}

impl AddAssign for Natural {
  #[inline]
  fn add_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) + rhs;
  }
}

impl Sub for Natural {
  type Output = Natural;

  #[inline]
  fn sub(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Natural(self.0 - rhs.0)
  }
}

impl SubAssign for Natural {
  #[inline]
  fn sub_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) - rhs;
  }
}

impl Mul for Natural {
  type Output = Natural;

  #[inline]
  fn mul(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Natural(self.0 * rhs.0)
  }
}

impl MulAssign for Natural {
  #[inline]
  fn mul_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) * rhs;
  }
}

impl Div for Natural {
  type Output = Natural;

  #[inline]
  fn div(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Natural(self.0 / rhs.0)
  }
}

impl DivAssign for Natural {
  #[inline]
  fn div_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) / rhs;
  }
}

impl Rem for Natural {
  type Output = Natural;

  #[inline]
  fn rem(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Natural(self.0 % rhs.0)
  }
}

impl RemAssign for Natural {
  #[inline]
  fn rem_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) % rhs;
  }
}

impl BitOr for Natural {
  type Output = Natural;

  #[inline]
  fn bitor(
    self, //.
    rhs: Self,
  ) -> Self::Output {
    Natural(self.0 | rhs.0)
  }
}

impl BitOrAssign for Natural {
  #[inline]
  fn bitor_assign(
    &mut self,
    rhs: Self, //.
  ) {
    *self = mem::take(self) | rhs;
  }
}

impl Shl<usize> for Natural {
  type Output = Natural;

  #[inline]
  fn shl(
    self, //.
    rhs: usize,
  ) -> Natural {
    Natural(self.0 << rhs)
  }
}

impl ShlAssign<usize> for Natural {
  #[inline]
  fn shl_assign(
    &mut self,
    rhs: usize, //.
  ) {
    *self = mem::take(self) << rhs;
  }
}

impl Shr<usize> for Natural {
  type Output = Natural;

  #[inline]
  fn shr(
    self, //.
    rhs: usize,
  ) -> Natural {
    Natural(self.0 >> rhs)
  }
}

impl ShrAssign<usize> for Natural {
  #[inline]
  fn shr_assign(
    &mut self,
    rhs: usize, //.
  ) {
    *self = mem::take(self) >> rhs;
  }
}

impl FromStr for Natural {
  type Err = ParseError;

  fn from_str(s: &str) -> Result<Natural, ParseError> {
    let num = s.strip_prefix('+').unwrap_or(s).trim_start_matches('0');
    Ok(Natural(Digits::parse(
      num, //.
      10,
    )?))
  }
}

impl From<u32> for Natural {
  /// Produce a natural from a [`u32`].
  fn from(n: u32) -> Self {
    Natural(Digits::Fix(
      n as u64, // fit
    ))
  }
}

impl From<u64> for Natural {
  /// Produce a natural from a [`u64`].
  fn from(n: u64) -> Self {
    Natural(Digits::Fix(
      n, // digit
    ))
  }
}

impl From<Dual> for Natural {
  /// Produce a natural from a dual (using its byte representation).
  fn from(dual: Dual) -> Self {
    let bytes = dual.to_le_bytes();
    Natural(Digits::from_le_bytes(&bytes))
  }
}

impl TryFrom<Natural> for u64 {
  type Error = ();

  fn try_from(n: Natural) -> Result<Self, Self::Error> {
    if let Digits::Fix(n) = n.0 {
      Ok(n)
    } else {
      Err(
        (), //.
      )
    }
  }
}

impl Default for Natural {
  /// The identity natural 0 (zero).
  fn default() -> Self {
    Natural::ZERO
  }
}

impl fmt::Display for Natural {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.pad_integral(true, "ℕ", &format!("{}", self.0))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn euclid() {
    type N = Natural;

    // trivial path: u, v = 0
    assert_eq!(N::gcd(N::from(5u64), N::from(0u64)), N::from(5u64));
    assert_eq!(N::lcm(N::from(5u64), N::from(0u64)), N::from(0u64));

    let m0 = N::from(13u64);
    let u0 = N::from(135u64);
    let v0 = N::from(36u64);

    // ```gcd(m*u, m*v) = m*gcd(u, v)```
    assert_eq!(
      N::gcd(m0.clone() * u0.clone(), m0.clone() * v0.clone()), //=
      m0.clone() * N::gcd(u0.clone(), v0.clone())
    );
    // ```gcd(u + m*v, v) = gcd(u, v)```
    assert_eq!(
      N::gcd(u0.clone() + m0.clone() * v0.clone(), v0.clone()), //=
      N::gcd(u0.clone(), v0.clone())
    );
    // commutative ```gcd(u, v) = gcd(v, u)```
    assert_eq!(
      N::gcd(u0.clone(), v0.clone()), //=
      N::gcd(v0.clone(), u0.clone())
    );
    // associative ```gcd(u, gcd(v, m)) = gcd(gcd(u, v), m)```
    assert_eq!(
      N::gcd(u0.clone(), N::gcd(v0.clone(), m0.clone())), //=
      N::gcd(N::gcd(u0.clone(), v0.clone()), m0.clone())
    );

    // ```lcm(u, gcd(u, v)) = u```
    assert_eq!(
      N::lcm(u0.clone(), N::gcd(u0.clone(), v0.clone())), //=
      u0.clone()
    );
    // ```lcm(u, v)*gcd(u, v) = u*v```
    assert_eq!(
      N::lcm(u0.clone(), v0.clone()) * N::gcd(u0.clone(), v0.clone()), //=
      u0.clone() * v0.clone()
    );
    // ```gcd(lcm(u, v), lcm(u, m)) = lcm(u, gcd(v, m))```
    assert_eq!(
      N::gcd(N::lcm(u0.clone(), v0.clone()), N::lcm(u0.clone(), m0.clone())), //=
      N::lcm(u0, N::gcd(v0, m0))
    );
  }
}
