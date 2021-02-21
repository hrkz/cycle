use crate::base::ring::repr::*;

/// Basic smallest domain, ℤ
pub type Integer = i128;

impl Domain for Integer {
  fn name(&self) -> String { String::from("ℤ") }

  fn num(&self) -> i128 { *self }
  fn den(&self) -> i128 { 1 }

  fn gcd(u: &Self, v: &Self) -> Self {
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

  fn lcm(u: &Self, v: &Self) -> Self {
    if u == &0 &&
      // 0 gcd and 
      // indeterminate lcm
       v == &0
    {
      return 0;
    }

    let gcd = Self::gcd(u, v);
    let lcm = (u * v) / gcd;
    lcm
  }
}

impl Ring for Integer {}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn dom() {
    // trivial path: u, v = 0
    assert_eq!(Domain::gcd(&5, &0), 5);
    assert_eq!(Domain::lcm(&5, &0), 0);
    // u = v
    assert_eq!(Domain::gcd(&3, &3), 3);
    assert_eq!(Domain::lcm(&3, &3), 3);
    // v % u = 0
    assert_eq!(Domain::gcd(&5, &25), 5);
    assert_eq!(Domain::lcm(&5, &25), 25);
    // v % u != 0
    assert_eq!(Domain::gcd(&7, &25), 1);
    assert_eq!(Domain::gcd(&4, &6), 2);
    assert_eq!(Domain::lcm(&7, &25), 175);
    assert_eq!(Domain::lcm(&4, &6), 12);

    let m0 = 13;
    let u0 = 135;
    let v0 = 36;

    // ```gcd(m*u, m*v) = m*gcd(u, v)```
    let u = m0 * u0;
    let v = m0 * v0;
    assert_eq!(Domain::gcd(&u, &v), m0 * Domain::gcd(&u0, &v0));
    // ```gcd(u + m*v, v) = gcd(u, v)```
    let u = u0 + m0 * v0;
    let v = v0;
    assert_eq!(Domain::gcd(&u, &v), Domain::gcd(&u0, &v0));
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
}
