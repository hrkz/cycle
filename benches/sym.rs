#![feature(test)]

extern crate test;

use cycle::*;
use test::Bencher;

#[bench]
fn trivial(b: &mut Bencher) {
  b.iter(|| Tree::ONE.add(Tree::NEG_ONE).trivial().expect("failed to apply `trivial` simplifications"));
}
