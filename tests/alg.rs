use cycle::*;

#[test]
fn quadratic_equation() -> Result<(), Form> {
  /// [Quadratic formula](https://en.wikipedia.org/wiki/Quadratic_formula)
  fn solve(a: Expr, b: Expr, c: Expr) -> (Expr, Expr) {
    let q2 = b.clone().pow(Expr::from(2)) - Expr::from(4) * a.clone() * c;
    let q1 = Expr::from(2) * a;

    let s1 = (-b.clone() + q2.clone().sqrt()) / q1.clone();
    let s2 = (-b - q2.sqrt()) / q1;
    (s1, s2)
  }

  let x = Expr::Sym(Symbol::new("x", Set::SR));

  let a = Expr::from(1);
  let b = Expr::from(-6);
  let c = Expr::from(5);

  // ```x^2 - 6*x + 5 = 0```
  let eq1 = a.clone() * x.clone().pow(Expr::from(2)) + b.clone() * x.clone() + c.clone();

  let (s1, s2) = solve(a, b, c);
  let mut sol1 = eq1.clone();
  // ```x = 1```
  sol1.subs(&x, &s1);
  let mut sol2 = eq1.clone();
  // ```x = 5```
  sol2.subs(&x, &s2);

  assert_eq!(sol1.trivial()?, Expr::ZERO);
  assert_eq!(sol2.trivial()?, Expr::ZERO);

  Ok(())
}
