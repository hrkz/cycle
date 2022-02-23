use crate::base::algebra::num_integer::Integer;

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A rational ℚ.
#[derive(Debug, Clone)]
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
    (self.num.is_negative() && self.den.is_positive()) || (self.num.is_positive() && self.den.is_negative())
  }

  /// Compute the Greatest Common Divisor (GCD) of two rationals `u` and `v`.
  pub fn gcd(u: Self, v: Self) -> Self {
    let (a, c) = (u.num, v.num);
    let (b, d) = (u.den, v.den);
    let ad = a * d.clone();
    let cb = c * b.clone();

    Rational::new(
      Integer::gcd(ad, cb), //.
      b * d,
    )
  }

  /// Compute the Lowest Common Multiple (LCM) of two rationals `u` and `v`.
  pub fn lcm(u: Self, v: Self) -> Self {
    let (a, c) = (u.num, v.num);
    let (b, d) = (u.den, v.den);

    Rational::new(
      Integer::lcm(a, c), //.
      Integer::gcd(b, d),
    )
  }
}

impl Eq for Rational {}
impl PartialEq for Rational {
  fn eq(&self, o: &Rational) -> bool {
    self.cmp(o) == Ordering::Equal
  }
}

impl PartialOrd for Rational {
  fn partial_cmp(&self, o: &Rational) -> Option<Ordering> {
    Some(self.cmp(o))
  }
}

impl Ord for Rational {
  fn cmp(
    &self,
    o: &Rational, // finite recursive quo/rem cmp
  ) -> Ordering {
    let (lhs_int, rhs_int) = (self.num.clone() / self.den.clone(), o.num.clone() / o.den.clone());
    let (lhs_rem, rhs_rem) = (self.num.clone() % self.den.clone(), o.num.clone() % o.den.clone());
    let int_cmp = lhs_int.cmp(&rhs_int);

    if int_cmp != Ordering::Equal {
      int_cmp
    } else {
      match (lhs_rem != Integer::ZERO, rhs_rem != Integer::ZERO) {
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
          let lhs_recip = Rational::new(self.den.clone(), lhs_rem);
          let rhs_recip = Rational::new(o.den.clone(), rhs_rem);
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
      Integer::ONE,
    )
  }
}

impl Add for Rational {
  type Output = Rational;

  /// ```a/b + c/d = (a*lcm/b + c*lcm/d)/lcm where lcm = lcm(b,d)```
  fn add(self, rhs: Self) -> Self::Output {
    let (a, c) = (self.num, rhs.num);
    let (b, d) = (self.den, rhs.den);

    let lcm = Integer::lcm(b.clone(), d.clone());
    Rational::new(
      a * lcm.clone() / b + c * lcm.clone() / d, //.
      lcm,
    )
  }
}

impl Sub for Rational {
  type Output = Rational;

  /// ```a/b - c/d = (lcm/b*a - lcm/d*c)/lcm, where lcm = lcm(b,d)```
  fn sub(self, rhs: Self) -> Self::Output {
    let (a, c) = (self.num, rhs.num);
    let (b, d) = (self.den, rhs.den);

    let lcm = Integer::lcm(b.clone(), d.clone());
    Rational::new(
      lcm.clone() / b * a - lcm.clone() / d * c, //.
      lcm,
    )
  }
}

impl Mul for Rational {
  type Output = Rational;

  /// ```a/b * c/d = (a/gcd_ad)*(c/gcd_bc) / ((d/gcd_ad)*(b/gcd_bc))```
  fn mul(self, rhs: Self) -> Self::Output {
    let (a, c) = (self.num, rhs.num);
    let (b, d) = (self.den, rhs.den);

    let gcd_ad = Integer::gcd(a.clone(), d.clone());
    let gcd_bc = Integer::gcd(b.clone(), c.clone());

    Rational::new(
      a / gcd_ad.clone() * c / gcd_bc.clone(), //.
      d / gcd_ad * b / gcd_bc,
    )
  }
}

impl Div for Rational {
  type Output = Rational;

  /// ```a/b / c/d = (a/gcd_ac)*(d/gcd_bd) / ((c/gcd_ac)*(b/gcd_bd))```
  fn div(self, rhs: Self) -> Self::Output {
    let (a, c) = (self.num, rhs.num);
    let (b, d) = (self.den, rhs.den);

    let gcd_ac = Integer::gcd(a.clone(), c.clone());
    let gcd_bd = Integer::gcd(b.clone(), d.clone());

    Rational::new(
      a / gcd_ac.clone() * d / gcd_bd.clone(), //.
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
  fn euclid() {
    type Z = Integer;
    type Q = Rational;

    // trivial path: u, v = 0
    assert_eq!(Q::gcd(Q::new(Z::from(1), Z::from(2)), Rational::from(Z::from(0))), Q::new(Z::from(1), Z::from(2)));
    assert_eq!(Q::lcm(Q::new(Z::from(1), Z::from(2)), Rational::from(Z::from(0))), Rational::from(Z::from(0)));

    let m0 = Q::new(Z::from(13), Z::from(121));
    let u0 = Q::new(Z::from(234), Z::from(19));
    let v0 = Q::new(Z::from(32), Z::from(7));

    // commutative ```gcd(u, v) = gcd(v, u)```
    assert_eq!(
      Q::gcd(u0.clone(), v0.clone()), //=
      Q::gcd(v0.clone(), u0.clone())
    );
    // associative ```gcd(u, gcd(v, m)) = gcd(gcd(u, v), m)```
    assert_eq!(
      Q::gcd(u0.clone(), Q::gcd(v0.clone(), m0.clone())), //=
      Q::gcd(Q::gcd(u0.clone(), v0.clone()), m0.clone())
    );

    // ```lcm(u, gcd(u, v)) = u```
    assert_eq!(
      Q::lcm(u0.clone(), Q::gcd(u0.clone(), v0.clone())), //=
      u0.clone()
    );
    // ```lcm(u, v)*gcd(u, v) = u*v```
    assert_eq!(
      Q::lcm(u0.clone(), v0.clone()) * Q::gcd(u0.clone(), v0.clone()), //=
      u0.clone() * v0.clone()
    );
    // ```lcm(u, gcd(v, m)) = gcd(lcm(u, v), lcm(u, m))```
    assert_eq!(
      Q::gcd(Q::lcm(u0.clone(), v0.clone()), Q::lcm(u0.clone(), m0.clone())), //=
      Q::lcm(u0, Q::gcd(v0, m0))
    );
  }

  #[test]
  fn ops() {
    type Z = Integer;
    type Q = Rational;

    let r1_1 = Q::from(Z::from(1));
    let r1_2 = Q::new(Z::from(1), Z::from(2));
    let r2_1 = Q::new(Z::from(2), Z::from(1));
    let n1_2 = Q::new(Z::from(-1), Z::from(2));
    let r3_7 = Q::new(Z::from(3), Z::from(7));
    let r9_4 = Q::new(Z::from(9), Z::from(4));

    // u = v
    assert_eq!(r1_2.clone() + r1_2.clone(), Q::new(Z::from(1), Z::from(1)));
    assert_eq!(r1_2.clone() * r1_2.clone(), Q::new(Z::from(1), Z::from(4)));
    // v = a/b, v = b/a
    assert_eq!(r1_2.clone() + r2_1.clone(), Q::new(Z::from(5), Z::from(2)));
    assert_eq!(r1_2.clone() * r2_1.clone(), Q::new(Z::from(1), Z::from(1)));
    // u = a/b, v = a/c
    assert_eq!(r1_2.clone() + r1_1.clone(), Q::new(Z::from(3), Z::from(2)));
    assert_eq!(r1_2.clone() * r1_1.clone(), Q::new(Z::from(1), Z::from(2)));
    // u = a/b, v = -a/b
    assert_eq!(r1_2.clone() + n1_2.clone(), Q::new(Z::from(0), Z::from(1)));
    assert_eq!(r1_2.clone() * n1_2.clone(), Q::new(Z::from(-1), Z::from(4)));
    // u = a/b, v = c/d
    assert_eq!(r3_7.clone() + r1_2.clone(), Q::new(Z::from(13), Z::from(14)));
    assert_eq!(r3_7.clone() * r1_2.clone(), Q::new(Z::from(3), Z::from(14)));
    assert_eq!(r3_7.clone() + r9_4.clone(), Q::new(Z::from(75), Z::from(28)));
    assert_eq!(r3_7.clone() * r9_4.clone(), Q::new(Z::from(27), Z::from(28)));

    // ```a/b * b/a = 1```
    assert_eq!(
      r3_7.clone() * Q::new(r3_7.den.clone(), r3_7.num.clone()), //=
      r1_1.clone()
    );
    assert_eq!(
      r9_4.clone() * Q::new(r9_4.den.clone(), r9_4.num.clone()), //=
      r1_1.clone()
    );

    // ```a/b - c/d = a/b + -c/d```
    assert_eq!(
      r3_7.clone() - r1_2.clone(), //=
      r3_7.clone() + r1_2.clone().neg()
    );
    assert_eq!(
      r3_7.clone() - r9_4.clone(), //=
      r3_7.clone() + r9_4.clone().neg()
    );

    // ```a/b / c/d = a/b * d/c```
    assert_eq!(
      r3_7.clone() / r1_2.clone(), //=
      r3_7.clone() * Q::new(r1_2.den.clone(), r1_2.num.clone())
    );
    assert_eq!(
      r3_7.clone() / r9_4.clone(), //=
      r3_7.clone() * Q::new(r9_4.den.clone(), r9_4.num.clone())
    );

    // commutative ```u + v = v + u, u * v = v * u```
    assert_eq!(
      r3_7.clone() + r9_4.clone(), //=
      r9_4.clone() + r3_7.clone()
    );
    assert_eq!(
      r3_7.clone() * r9_4.clone(), //=
      r9_4.clone() * r3_7.clone()
    );
    // associative ```m + (u + v) = (m + u) + v, m * (u * v) = (m * u) * v```
    assert_eq!(
      n1_2.clone() + (r3_7.clone() + r9_4.clone()), //=
      (n1_2.clone() + r9_4.clone()) + r3_7.clone()
    );
    assert_eq!(
      n1_2.clone() * (r3_7.clone() * r9_4.clone()), //=
      (n1_2.clone() * r9_4.clone()) * r3_7.clone()
    );
  }
}
