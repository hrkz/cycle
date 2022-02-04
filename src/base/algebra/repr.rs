use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait Domain
  : Clone
  // ops
  + Add<Output = Self>
  + Sub<Output = Self>
  + Mul<Output = Self>
  + Div<Output = Self>
  + Neg
{
  fn name(&self) -> String;

  fn num(&self) -> i128;
  fn den(&self) -> i128;

  fn gcd(u: &Self, u: &Self) -> Self;
  fn lcm(v: &Self, v: &Self) -> Self;

  fn cofactors(&self, u: &Self, v: &Self) -> (Self, Self, Self) {
    let gcd = Self::gcd(u, v);
    let cfa = u.clone() / gcd.clone();
    let cfb = v.clone() / gcd.clone();
    (gcd, cfa, cfb)
  }
}

/// A trait to represent algebraic structures (underlying set and corresponding allowed operations).
pub trait Theory {}

/// An abstract structure annotation.
#[derive(Debug, Clone, Hash, PartialEq, PartialOrd, Eq, Ord, Copy)]
pub enum Structure {
  /// Abstract
  AS,
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
  /// Custom
  SR,
}
