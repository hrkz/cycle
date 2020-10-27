use std::fmt;

use crate::{Expr, SymbolicResult};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Special {
  /// ```$(f \circ g)(x)$```
  Comp(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Function {
  MapExpr {
    name: String,
    arg: Vec<Expr>,
  },

  SpeExpr(
    //.
    Special,
  ),
}

impl Function {
  pub fn trivial(self) -> SymbolicResult<Expr> { Ok(Expr::Rel(self)) }

  pub fn subs(&self, m: &Expr, s: &Expr) -> Expr {
    match self {
      Function::MapExpr {
        //.
        name,
        arg,
      } => Expr::Rel(Function::MapExpr {
        name: name.clone(),
        arg: arg.iter().map(|x| x.subs(m, s)).collect(),
      }),

      Function::SpeExpr(
        //.
        map,
      ) => match map {
        Special::Comp(lhs, rhs) => Expr::Rel(Function::SpeExpr(Special::Comp(Box::new(lhs.subs(m, s)), Box::new(rhs.subs(m, s))))),
      },
    }
  }
}

impl fmt::Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Function::MapExpr {
        //.
        name,
        arg,
      } => {
        let mut iter = arg.iter();
        if let Some(e) = iter.next() {
          write!(f, "{}({})", name, iter.fold(format!("{}", e), |acc, e| acc + &format!(", {}", e)))
        } else {
          write!(f, "{}()", name)
        }
      }

      Function::SpeExpr(
        //.
        map,
      ) => match map {
        Special::Comp(lhs, rhs) => write!(f, "{} ∘ {}", lhs, rhs),
      },
    }
  }
}

impl Expr {
  /// ```map(x_1, ..., x_n)
  pub fn r#map(name_str: &str, arg: Vec<Expr>) -> Self {
    let name = name_str.replace(&[' ', '+', '-', '*', '/', '^', '=', '(', ')', '{', '}', '#', '~'][..], "");
    // any non-whitespace, non-special character
    assert_eq!(name, name_str);

    Self::Rel(Function::MapExpr {
      //.
      name,
      arg,
    })
  }
}
