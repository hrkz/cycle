use crate::base::ring::num_integer::Integer;
use crate::base::ring::repr::*;

use std::cmp::Ordering;
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Debug, Clone, Copy)]
pub struct Rational {
  num: Integer,
  den: Integer,
}

impl Rational {
  #[inline]
  pub const fn new(num: Integer, den: Integer) -> Rational {
    Rational {
      // Q
      num,
      den,
    }
  }

  pub fn zero() -> Rational { Rational::new(0, 1) }
  pub fn unit() -> Rational { Rational::new(1, 1) }

  // decompose
  // self = self.trunc() + self.fract()

  pub fn trunc(&self) -> Rational {
    Rational::from(self.num / self.den) //.
  }

  pub fn fract(&self) -> Rational {
    Rational::new(
      //.
      self.num % self.den,
      self.den,
    )
  }

  pub fn is_positive(&self) -> bool { (self.num > 0 && self.den > 0) || (self.num < 0 && self.den < 0) }
  pub fn is_negative(&self) -> bool { (self.num < 0 && self.den > 0) || (self.num > 0 && self.den < 0) }
}

impl Domain for Rational {
  fn name(self) -> String { "QQ".to_string() }

  fn num(self) -> i64 { self.num }
  fn den(self) -> i64 { self.den }

  /// ```gcd(a/b, c/d) = gcd(a*d, c*b)/(b*d)```
  fn gcd(u: Self, v: Self) -> Self {
    let (a, c) = (u.num, v.num);
    let (b, d) = (u.den, v.den);

    Self::new(
      //.
      Integer::gcd(a * d, c * b),
      b * d,
    )
  }

  /// ```lcm(a/b, c/d) = lcm(a, c)/gcd(b, d)```
  fn lcm(u: Self, v: Self) -> Self {
    let (a, c) = (u.num, v.num);
    let (b, d) = (u.den, v.den);

    Self::new(
      //.
      Integer::lcm(a, c),
      Integer::gcd(b, d),
    )
  }
}

impl Ring for Rational {}
impl Field for Rational {}

impl PartialEq for Rational {
  fn eq(&self, other: &Rational) -> bool { self.cmp(other) == Ordering::Equal }
}

impl Eq for Rational {}
impl PartialOrd for Rational {
  fn partial_cmp(&self, other: &Rational) -> Option<Ordering> { Some(self.cmp(other)) }
}

impl Ord for Rational {
  fn cmp(
    &self,
    other: &Rational, //. finite recursive quo/rem cmp
  ) -> Ordering {
    let (lhs_int, rhs_int) = (self.num / self.den, other.num / other.den);
    let (lhs_rem, rhs_rem) = (self.num % self.den, other.num % other.den);
    let int_cmp = lhs_int.cmp(&rhs_int);

    if int_cmp != Ordering::Equal {
      int_cmp
    } else {
      match (lhs_rem != 0, rhs_rem != 0) {
        (false, false) => {
          Ordering::Equal //.
        }
        (false, true) => {
          Ordering::Less //.
        }
        (true, false) => {
          Ordering::Greater //.
        }
        (true, true) => {
          // a/(a % b) < c/(c % d)
          let lhs_recip = Rational::new(self.den, lhs_rem);
          let rhs_recip = Rational::new(other.den, rhs_rem);
          lhs_recip.cmp(&rhs_recip).reverse()
        }
      }
    }
  }
}

impl From<Integer> for Rational {
  fn from(n: Integer) -> Self { Rational { num: n, den: 1 } }
}

impl Add for Rational {
  type Output = Rational;

  /// ```a/b + c/d = (a*lcm/b + c*lcm/d)/lcm where lcm = lcm(b,d)```
  fn add(self, o: Self) -> Self::Output {
    let (a, c) = (self.num, o.num);
    let (b, d) = (self.den, o.den);

    let lcm = Integer::lcm(b, d);
    Rational::new(
      //.
      a * lcm / b + c * lcm / d,
      lcm,
    )
  }
}

impl Sub for Rational {
  type Output = Rational;

  /// ```a/b - c/d = (lcm/b*a - lcm/d*c)/lcm, where lcm = lcm(b,d)```
  fn sub(self, o: Self) -> Self::Output {
    let (a, c) = (self.num, o.num);
    let (b, d) = (self.den, o.den);

    let lcm = Integer::lcm(b, d);
    Rational::new(
      //.
      lcm / b * a - lcm / d * c,
      lcm,
    )
  }
}

impl Mul for Rational {
  type Output = Rational;

  /// ```a/b * c/d = (a/gcd_ad)*(c/gcd_bc) / ((d/gcd_ad)*(b/gcd_bc))```
  fn mul(self, o: Self) -> Self::Output {
    let (a, c) = (self.num, o.num);
    let (b, d) = (self.den, o.den);

    let gcd_ad = Integer::gcd(a, d);
    let gcd_bc = Integer::gcd(b, c);

    Rational::new(
      //.
      a / gcd_ad * c / gcd_bc,
      d / gcd_ad * b / gcd_bc,
    )
  }
}

impl Div for Rational {
  type Output = Rational;

  /// ```a/b / c/d = (a/gcd_ac)*(d/gcd_bd) / ((c/gcd_ac)*(b/gcd_bd))```
  fn div(self, o: Self) -> Self::Output {
    let (a, c) = (self.num, o.num);
    let (b, d) = (self.den, o.den);

    let gcd_ac = Integer::gcd(a, c);
    let gcd_bd = Integer::gcd(b, d);

    Rational::new(
      //.
      a / gcd_ac * d / gcd_bd,
      c / gcd_ac * b / gcd_bd,
    )
  }
}

impl Neg for Rational {
  type Output = Rational;

  fn neg(self) -> Rational { Rational::new(-self.num, self.den) }
}
