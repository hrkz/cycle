use cycle::*;

#[test]
fn fmt() {
  // Integer ℤ
  assert_eq!(format!("{}", Tree::Num(Number::Z(19))), "19");
  assert_eq!(format!("{}", Tree::Num(Number::Z(-3))), "-3");
  // Rational ℚ
  assert_eq!(format!("{}", Tree::Num(Number::Q(Rational::new(9, 4)))), "9/4");
  assert_eq!(format!("{}", Tree::Num(Number::Q(Rational::new(-1, 2)))), "-1/2");
  assert_eq!(format!("{}", Tree::Num(Number::Q(Rational::new(3, -4)))), "3/-4");

  // Symbols
  let x = Tree::Sym(Symbol::new("x", Structure::SR).expect("failed to create symbol `x`"));
  let y = Tree::Sym(Symbol::new("y", Structure::SR).expect("failed to create symbol `y`"));
  let z = Tree::Sym(Symbol::new("z", Structure::SR).expect("failed to create symbol `z`"));

  assert_eq!(format!("{}", x), "x");
  assert_eq!(format!("{}", y), "y");
  assert_eq!(format!("{}", z), "z");

  // Add
  assert_eq!(format!("{}", x.clone().add(Tree::Num(Number::Z(1)))), "x + 1");
  assert_eq!(format!("{}", y.clone().add(z.clone())), "y + z");
  // Mul
  assert_eq!(format!("{}", x.clone().mul(Tree::Num(Number::Z(3)))), "x*3");
  assert_eq!(format!("{}", z.clone().mul(y.clone())), "z*y");
  // Pow
  assert_eq!(format!("{}", x.clone().pow(Tree::Num(Number::Z(3)))), "x^3");
  assert_eq!(format!("{}", x.clone().pow(Tree::Num(Number::Q(Rational::new(-9, 4))))), "x^(-9/4)");
  assert_eq!(format!("{}", x.clone().pow(y.clone().pow(z.clone()))), "x^y^z");
  assert_eq!(format!("{}", x.clone().pow(y.clone()).pow(z.clone())), "x^y^z");
  // Fact
  assert_eq!(format!("{}", x.clone().fact()), "x!");

  // Compound
}

#[test]
fn parse() -> Result<(), lang::Error> {
  assert_eq!(lang::parse("1 + 1")?, Tree::from(1).add(Tree::from(1)));
  Ok(())
}

#[test]
fn eval() -> Result<(), lang::Error> {
  Ok(())
}
