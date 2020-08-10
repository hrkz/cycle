use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait Domain
  : Clone
  + Copy
  //. ops
  + Add<Output = Self>
  + Sub<Output = Self>
  + Mul<Output = Self>
  + Div<Output = Self>
  + Neg
{
  fn name(self) -> String;

  fn num(self) -> i64;
  fn den(self) -> i64;

  fn gcd(u: Self, u: Self) -> Self;
  fn lcm(v: Self, v: Self) -> Self;

  fn cofactors(self, u: Self, v: Self) -> (Self, Self, Self) {
    let gcd = Self::gcd(u, v);
    let cfa = u / gcd;
    let cfb = v / gcd;
    (gcd, cfa, cfb)
  }
}

pub trait Ring
  : Domain
  // associativity
  + PartialEq
{
}

pub trait Field
  : Ring
  // commutativity
  + PartialOrd
{
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq)]
pub enum Set {
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
