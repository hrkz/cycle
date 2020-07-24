//use crate::base::ring::num_integer;

use std::cmp::Ordering;

#[derive(Debug, Clone)]
pub struct Rational {
  pub num: i64,
  pub den: i64,
}

impl Rational {
  pub fn new(num: i64, den: i64) -> Rational {
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

impl From<i64> for Rational {
  fn from(n: i64) -> Self { Rational { num: n, den: 1 } }
}
