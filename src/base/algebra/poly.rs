use std::cmp::Ordering;

use crate::Tree;

// Orderings
pub fn order_expr<'t, L, R>(
  //.
  lhs: L,
  rhs: R,
) -> Ordering
where
  L: Iterator<Item = &'t Tree>,
  R: Iterator<Item = &'t Tree>,
{
  let mut lhs = lhs.filter(|e| !e.is_value());
  let mut rhs = rhs.filter(|e| !e.is_value());

  loop {
    match (lhs.next(), rhs.next()) {
      (Some(l), Some(r)) => {
        let c = l.cmp(r);
        if c != Ordering::Equal {
          return c;
        }
      }

      (l, r) => {
        return r.cmp(
          &l, //.
        );
      }
    }
  }
}
