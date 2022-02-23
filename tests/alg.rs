use cycle::*;

#[test]
fn quadratic_equation() -> Result<(), Form> {
  /// [Quadratic formula](https://en.wikipedia.org/wiki/Quadratic_formula)
  fn solve(a: Tree, b: Tree, c: Tree) -> (Tree, Tree) {
    let q2 = b.clone().pow(Tree::from(2)).sub(Tree::from(4).mul(a.clone()).mul(c));
    let q1 = Tree::from(2).mul(a);

    let s1 = (b.clone().neg().add(q2.clone().sqrt())).div(q1.clone());
    let s2 = (b.neg().sub(q2.sqrt())).div(q1);
    (s1, s2)
  }

  let x = Tree::Sym(Symbol::new("x", Number::C).expect("failed to declare symbol `x`"));

  let a = Tree::from(1);
  let b = Tree::from(-6);
  let c = Tree::from(5);

  // ```x^2 + -6*x + 5 = 0```
  let eq1 = x.clone().pow(Tree::from(2)).add(b.clone().mul(x.clone()).add(c.clone()));

  let (s1, s2) = solve(a, b, c);
  let mut sol1 = eq1.clone();
  // ```x = 1```
  sol1.subs(&x, &s1);
  let mut sol2 = eq1.clone();
  // ```x = 5```
  sol2.subs(&x, &s2);

  assert_eq!(sol1.trivial()?, Tree::ZERO);
  assert_eq!(sol2.trivial()?, Tree::ZERO);

  Ok(())
}
