mod parse;
mod token;

pub use parse::Parser;
pub use token::{Lexer, Token, TokenKeyword, TokenKind};

use crate::base::Expr;

use std::collections::HashMap;
use std::fmt;
use std::ops;

#[derive(Debug, Clone)]
pub enum Ast {
  Expr(Expr),

  /// ```x = y```
  Assign(Expr, Expr),
  //
  // Extension
  // (Load)
  // (Mod)
  //
}

#[derive(Debug, Clone)]
pub struct Interpreter {
  symbols: HashMap<Expr, Expr>,
  version: u32,
}

impl Interpreter {
  pub fn new(version: u32) -> Interpreter {
    Interpreter {
      //.
      symbols: HashMap::new(),
      version,
    }
  }

  pub fn eval(&mut self, stmt: &str) -> Result<Option<Expr>, LangError> {
    if stmt.is_empty() {
      return Ok(None);
    }

    match Parser::parse(stmt)? {
      Ast::Expr(expr) => {
        // lookup
        Ok(Some(self.resolve(&expr)))
      }

      Ast::Assign(lhs, rhs) => {
        if !lhs.iter().any(|expr| matches!(expr, Expr::Sym(_))) {
          return Err(LangError::Rule {
            rule: "can not assign to constant expression",
          });
        }

        if rhs.free(&lhs) {
          let rhs = self.resolve(&rhs);
          self.symbols.insert(
            lhs, //.
            rhs,
          );

          Ok(None)
        } else {
          Err(
            //.
            LangError::Rec,
          )
        }
      }
    }
  }

  fn resolve(&mut self, lhs: &Expr) -> Expr {
    lhs.iter().filter_map(|sub| self.symbols.get(&sub).map(|res| (sub, res))).fold(lhs.clone(), |expr, (sub, res)| {
      expr.subs(
        &sub, //.
        &res,
      )
    })
  }
}

pub type Span = ops::Range<usize>;

use std::num::ParseIntError;

#[derive(Debug, Clone)]
pub enum LangError {
  /// Lexical error
  Lex,
  /// End error
  End,
  /// Recursive error
  Rec,
  /// Rule error
  Rule {
    //.
    rule: &'static str,
  },

  /// Parsing integer error
  Integer { err: ParseIntError, span: Span },

  /// Unexpected operator
  Expected {
    //.
    expr: &'static str,
    span: Span,
  },
}

impl fmt::Display for LangError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      LangError::Lex => write!(f, "invalid syntax"),
      LangError::End => write!(f, "unexpected end of statement"),
      LangError::Rec => write!(f, "recursive assignment detected"),

      LangError::Rule { rule } => write!(f, "rule inconsistency ({})", rule),

      LangError::Integer {
        //.
        err,
        span,
      } => {
        write!(
          f,
          "failed to parse integer ({}) [at {:?}]", //.
          err, span
        )
      }

      LangError::Expected {
        //.
        expr,
        span,
      } => {
        write!(
          f,
          "expected {} [at {:?}]", //.
          expr, span
        )
      }
    }
  }
}
