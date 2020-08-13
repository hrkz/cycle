use crate::base::ring::repr::*;

/// Basic smallest domain, Z
pub type Integer = i128;

trait Arithmetic {
  fn is_multiple_of(&self) -> bool;
  fn is_prime(&self) -> bool;
  fn is_perfect(&self) -> bool;
  fn is_palindrome(&self) -> bool;

  fn primes(&self) -> &[Integer];
  fn factors(&self) -> &[Integer];
}

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
impl Field for Integer {}
