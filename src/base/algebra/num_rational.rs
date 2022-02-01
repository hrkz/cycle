use crate::base::algebra::num_integer::Integer;
use crate::base::algebra::repr::*;

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A rational ℚ.
#[derive(Debug, Clone, Copy)]
pub struct Rational {
  /// Numerator.
  pub(crate) num: Integer,
  /// Denominator.
  pub(crate) den: Integer,
}

impl Rational {
  /// Create a new [`Rational`].
  pub const fn new(num: Integer, den: Integer) -> Rational {
    Rational {
      // Q
      num,
      den,
    }
  }

  /// Return `true` if `self` has a positive sign.
  pub fn is_positive(&self) -> bool {
    !self.is_negative()
  }
  /// Return `true` if `self` has a negative sign.
  pub fn is_negative(&self) -> bool {
    (self.num < 0 && self.den > 0) || (self.num > 0 && self.den < 0)
  }
}

impl Domain for Rational {
  fn name(&self) -> String {
    String::from("ℚ")
  }

  fn num(&self) -> Integer {
    self.num
  }
  fn den(&self) -> Integer {
    self.den
  }

  /// ```gcd(a/b, c/d) = gcd(a*d, c*b)/(b*d)```
  fn gcd(u: &Self, v: &Self) -> Self {
    let (a, c) = (u.num, v.num);
    let (b, d) = (u.den, v.den);
    let ad = a * d;
    let cb = c * b;

    Self::new(
      Integer::gcd(&ad, &cb), //.
      b * d,
    )
  }

  /// ```lcm(a/b, c/d) = lcm(a, c)/gcd(b, d)```
  fn lcm(u: &Self, v: &Self) -> Self {
    let (a, c) = (u.num, v.num);
    let (b, d) = (u.den, v.den);

    Self::new(
      Integer::lcm(&a, &c), //.
      Integer::gcd(&b, &d),
    )
  }
}

impl Eq for Rational {}
impl PartialEq for Rational {
  fn eq(&self, other: &Rational) -> bool {
    self.cmp(other) == Ordering::Equal
  }
}

impl PartialOrd for Rational {
  fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Rational {
  fn cmp(
    &self,
    other: &Rational, // finite recursive quo/rem cmp
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
          // ```a/(a % b) < c/(c % d)```
          let lhs_recip = Rational::new(self.den, lhs_rem);
          let rhs_recip = Rational::new(other.den, rhs_rem);
          lhs_recip.cmp(&rhs_recip).reverse()
        }
      }
    }
  }
}

impl Hash for Rational {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.num.hash(state);
    self.den.hash(state);
  }
}

impl From<Integer> for Rational {
  fn from(n: Integer) -> Self {
    Rational::new(
      n, //.
      1,
    )
  }
}

impl Add for Rational {
  type Output = Rational;

  /// ```a/b + c/d = (a*lcm/b + c*lcm/d)/lcm where lcm = lcm(b,d)```
  fn add(self, o: Self) -> Self::Output {
    let (a, c) = (self.num, o.num);
    let (b, d) = (self.den, o.den);

    let lcm = Integer::lcm(&b, &d);
    Rational::new(
      a * lcm / b + c * lcm / d, //.
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

    let lcm = Integer::lcm(&b, &d);
    Rational::new(
      lcm / b * a - lcm / d * c, //.
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

    let gcd_ad = Integer::gcd(&a, &d);
    let gcd_bc = Integer::gcd(&b, &c);

    Rational::new(
      a / gcd_ad * c / gcd_bc, //.
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

    let gcd_ac = Integer::gcd(&a, &c);
    let gcd_bd = Integer::gcd(&b, &d);

    Rational::new(
      a / gcd_ac * d / gcd_bd, //.
      c / gcd_ac * b / gcd_bd,
    )
  }
}

impl Neg for Rational {
  type Output = Rational;

  fn neg(self) -> Self::Output {
    Rational::new(
      self.num.neg(), //.
      self.den,
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn dom() {
    let r1_2 = Rational::new(1, 2);
    let r2_1 = Rational::new(2, 1);
    let r2_5 = Rational::new(2, 5);
    let r4_5 = Rational::new(4, 5);
    let r7_2 = Rational::new(7, 2);
    let r3_9 = Rational::new(3, 9);

    // trivial path: u, v = 0
    assert_eq!(Domain::gcd(&r1_2, &Rational::from(0)), r1_2);
    assert_eq!(Domain::lcm(&r1_2, &Rational::from(0)), Rational::from(0));
    // u = v
    assert_eq!(Domain::gcd(&r2_5, &r2_5), r2_5);
    assert_eq!(Domain::lcm(&r2_5, &r2_5), r2_5);
    // v % u = 0
    assert_eq!(Domain::gcd(&r2_5, &r4_5), r2_5);
    assert_eq!(Domain::lcm(&r2_5, &r4_5), r4_5);
    // v % u != 0
    assert_eq!(Domain::gcd(&r7_2, &r4_5), Rational::new(1, 10));
    assert_eq!(Domain::gcd(&r1_2, &r3_9), Rational::new(3, 18));
    assert_eq!(Domain::lcm(&r2_5, &r7_2), Rational::new(14, 1));
    assert_eq!(Domain::lcm(&r3_9, &r2_1), Rational::new(6, 1));

    let m0 = Rational::new(13, 121);
    let u0 = Rational::new(234, 19);
    let v0 = Rational::new(32, 7);

    // commutative ```gcd(u, v) = gcd(v, u)```
    assert_eq!(Domain::gcd(&u0, &v0), Domain::gcd(&v0, &u0));
    // associative ```gcd(u, gcd(v, m)) = gcd(gcd(u, v), m)```
    assert_eq!(Domain::gcd(&u0, &Domain::gcd(&v0, &m0)), Domain::gcd(&Domain::gcd(&u0, &v0), &m0));

    // ```lcm(u, gcd(u, v)) = u```
    assert_eq!(Domain::lcm(&u0, &Domain::gcd(&u0, &v0)), u0);
    // ```lcm(u, gcd(v, m)) = gcd(lcm(u, v), lcm(u, m))```
    assert_eq!(Domain::lcm(&u0, &Domain::gcd(&v0, &m0)), Domain::gcd(&Domain::lcm(&u0, &v0), &Domain::lcm(&u0, &m0)));
    // ```lcm(u, v)*gcd(u, v) = u*v```
    assert_eq!(Domain::lcm(&u0, &v0) * Domain::gcd(&u0, &v0), u0 * v0);
  }

  #[test]
  fn ops() {
    let r1_1 = Rational::from(1);
    let r1_2 = Rational::new(1, 2);
    let r2_1 = Rational::new(2, 1);
    let n1_2 = Rational::new(-1, 2);
    let r3_7 = Rational::new(3, 7);
    let r9_4 = Rational::new(9, 4);

    // u = v
    assert_eq!(r1_2 + r1_2, Rational::new(1, 1));
    assert_eq!(r1_2 * r1_2, Rational::new(1, 4));
    // a/b = b/a
    assert_eq!(r1_2 + r2_1, Rational::new(5, 2));
    assert_eq!(r1_2 * r2_1, Rational::new(1, 1));
    // a/b = a/c
    assert_eq!(r1_2 + r1_1, Rational::new(3, 2));
    assert_eq!(r1_2 * r1_1, Rational::new(1, 2));
    // a/b = -a/b
    assert_eq!(r1_2 + n1_2, Rational::new(0, 1));
    assert_eq!(r1_2 * n1_2, Rational::new(-1, 4));
    // a/b = c/d
    assert_eq!(r3_7 + r1_2, Rational::new(13, 14));
    assert_eq!(r3_7 * r1_2, Rational::new(3, 14));
    assert_eq!(r3_7 + r9_4, Rational::new(75, 28));
    assert_eq!(r3_7 * r9_4, Rational::new(27, 28));

    // ```a/b - c/d = a/b + -c/d```
    assert_eq!(r3_7 - r1_2, r3_7 + r1_2.neg());
    assert_eq!(r3_7 - r9_4, r3_7 + r9_4.neg());

    // ```a/b / c/d = a/b * d/c```
    assert_eq!(r3_7 / r1_2, r3_7 * Rational::new(r1_2.den, r1_2.num));
    assert_eq!(r3_7 / r9_4, r3_7 * Rational::new(r9_4.den, r9_4.num));
  }
}
