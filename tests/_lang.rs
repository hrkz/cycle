#![cfg(feature = "cycle_lang")]

use cycle::*;

#[test]
fn parse() -> Result<(), lang::Error> {
  assert_eq!(lang::parse("1 + 1")?, Tree::from(1).add(Tree::from(1)));
  Ok(())
}

#[test]
fn eval() -> Result<(), lang::Error> {
  Ok(())
}
