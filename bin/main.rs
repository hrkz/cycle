/*
 Cycle v0.0.1
 [main]
 Copyright (c) 2020-present, Hugo (hrkz) Frezat
*/

/// @see wiki
/// http://cycle-research.org
use cycle::*;

fn main() {
  println!("Hello Cycle! Currently ver. 0/1, or {:?}...", Number::Q(Rational::new(0, 1)).trivial());
}