use std::cmp::Ordering;
use std::fmt;

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord)]
enum Sign {
  Pos,
  Neg,
}

#[derive(Debug)]
pub struct Integer {
  sign: Sign,
  data: Vec<u64>,
}

impl Integer {
  // to i64 -> Option<i64>
  pub fn zero() -> Integer { Integer::from(0) }
  pub fn unit() -> Integer { Integer::from(1) }

  pub fn is_positive(&self) -> bool { self.sign == Sign::Pos }
  pub fn is_negative(&self) -> bool { self.sign == Sign::Neg }
}

impl PartialEq for Integer {
  fn eq(&self, other: &Integer) -> bool { self.sign == other.sign && self.data == other.data }
}

impl Eq for Integer {}
impl PartialOrd for Integer {
  fn partial_cmp(&self, other: &Integer) -> Option<Ordering> { Some(self.cmp(other)) }
}

impl Ord for Integer {
  fn cmp(
    &self,
    other: &Integer, //. cmp sign + data
  ) -> Ordering {
    let sign = self
      //. sgn
      .sign
      .cmp(&other.sign);
    if sign != Ordering::Equal {
      return sign;
    }

    match self.sign {
      Sign::Pos => self.data.cmp(&other.data),
      Sign::Neg => other.data.cmp(&self.data),
    }
  }
}

impl From<u64> for Integer {
  fn from(n: u64) -> Self { Integer { sign: Sign::Pos, data: vec![n] } }
}

impl fmt::Display for Integer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.pad_integral(!self.is_negative(), "", &self.data.iter().map(|i| i.to_string()).collect::<String>()) }
}

/// Number Theory
pub fn gcd(u: i64, v: i64) -> i64 {
  let u = u.abs();
  let v = v.abs();

  match (u, v) {
    (0, v) => v,
    (u, 0) => u,

    (u, v) => {
      let s = (u | v).trailing_zeros();

      let mut u = u;
      let mut v = v;

      u >>= u.trailing_zeros();

      while v != 0 {
        v >>= v.trailing_zeros();

        if u > v {
          std::mem::swap(&mut u, &mut v);
        }

        v -= u;
      }

      u << s
    }
  }
}

pub fn gcd_lcm(u: i64, v: i64) -> (i64, i64) {
  if u == 0 &&
    // 0 gcd and 
    // indeterminate lcm
     v == 0
  {
    return (0, 0);
  }

  let gcd = gcd(u, v);
  let lcm = u * (v / gcd);
  (gcd, lcm)
}
