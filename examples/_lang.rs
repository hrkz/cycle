use cycle::*;

use lang::LangError;

#[test]
fn fmt() {
  // Integer ℤ
  assert_eq!(format!("{}", Expr::Num(Number::Z(19))), "19");
  assert_eq!(format!("{}", Expr::Num(Number::Z(-3))), "-3");
  // Rational ℚ
  assert_eq!(format!("{}", Expr::Num(Number::Q(Rational::new(9, 4)))), "9/4");
  assert_eq!(format!("{}", Expr::Num(Number::Q(Rational::new(-1, 2)))), "-1/2");
  assert_eq!(format!("{}", Expr::Num(Number::Q(Rational::new(3, -4)))), "3/-4");

  // Symbols
  let x = Expr::Sym(Symbol::new("x", Set::SR));
  let y = Expr::Sym(Symbol::new("y", Set::SR));
  let z = Expr::Sym(Symbol::new("z", Set::SR));

  assert_eq!(format!("{}", x), "x");
  assert_eq!(format!("{}", y), "y");
  assert_eq!(format!("{}", z), "z");
  assert_eq!(format!("{}", Expr::Sym(Symbol::new("x0", Set::SR))), "x0");

  // Add
  assert_eq!(format!("{}", x.clone() + Expr::Num(Number::Z(1))), "x + 1");
  assert_eq!(format!("{}", y.clone() + z.clone()), "y + z");
  // Mul
  assert_eq!(format!("{}", x.clone() * Expr::Num(Number::Z(3))), "x*3");
  assert_eq!(format!("{}", z.clone() * y.clone()), "z*y");
  // Power
  assert_eq!(format!("{}", x.clone().pow(Expr::Num(Number::Z(3)))), "x^3");
  assert_eq!(format!("{}", x.clone().pow(Expr::Num(Number::Q(Rational::new(-9, 4))))), "x^(-9/4)");
  assert_eq!(format!("{}", x.clone().pow(y.clone().pow(z.clone()))), "x^y^z");
  assert_eq!(format!("{}", x.clone().pow(y.clone()).pow(z.clone())), "x^y^z");
  // Factorial
  assert_eq!(format!("{}", x.clone().fact()), "x!");

  // Compound
}

#[test]
fn parse() -> Result<(), LangError> {
  assert_eq!(lang::parse("1 + 1")?, Expr::from(1) + Expr::from(1));

  Ok(())
}

#[test]
fn exec() -> Result<(), LangError> { Ok(()) }
