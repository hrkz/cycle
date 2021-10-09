mod parse;
mod token;

pub use parse::Parser;
pub use token::{Lexer, Token, TokenKind};

use crate::{Expr, Function};

use std::collections::HashMap;
use std::fmt;
use std::ops;

///
/// cycle-lang spec
///
/// The reference is described mainly as a mathematical language with special operators.
/// Note that this is intended to help the user
/// when interacting with the interpreter.
///
/// # Built-in
///
/// The following expressions are defined within the library.
/// A complete cheat-sheet will soon bring more details about these,
/// with direct correspondance between the cycle syntax and its corresponding mathematical operation.
///
/// - Elementary functions, including trigonometric, hyperbolic and exponential families.
/// - [Mathematical constants](crate::Constant).
///
/// # Examples
///

#[derive(Debug, Clone)]
pub enum Ast {
  Expr(Expr),

  /// ```x := y```
  Rule(Expr, Expr),
  /// ```f(x_) = g(x_)```
  Def(Expr, Expr),
  //
  // Extension
  // (Load)
  // (Mod)
  //
}

#[derive(Debug)]
struct Rule {
  map: Expr,
}

#[derive(Debug)]
struct Definition {
  map: Expr,
  arg: Vec<Expr>,
}

pub type Builtin = fn(Vec<Expr>) -> Result<Expr, (usize, usize)>;

#[derive(Debug)]
pub struct Session {
  f: HashMap<String, Builtin>,
  prev: Option<Expr>,
}

#[derive(Debug)]
pub struct Interpreter {
  env: (HashMap<Expr, Rule>, HashMap<String, Definition>),
  ses: Session,
}

impl Interpreter {
  pub fn new() -> Interpreter {
    Interpreter {
      //.
      env: (HashMap::new(), HashMap::new()),
      ses: Session {
        //.
        f: HashMap::new(),
        prev: None,
      },
    }
  }

  pub fn bind_function(&mut self, name: &str, f: Builtin) { self.ses.f.insert(String::from(name), f); }

  pub fn parse(&mut self, stmt: &str) -> Result<Option<Expr>, LangError> {
    if stmt.is_empty() {
      return Ok(None);
    }

    self.eval(Parser::parse(
      stmt, &self.ses, //.
    )?)
  }

  pub fn eval(&mut self, ast: Ast) -> Result<Option<Expr>, LangError> {
    match ast {
      Ast::Expr(expr) => {
        // lookup
        Ok(Some(self.ses.prev.insert(self.compose(expr)?).clone()))
      }

      Ast::Rule(lhs, rhs) => {
        if matches!(lhs, Expr::Num(_)) {
          return Err(LangError::Rule {
            rule: format!("rule require a non-constant expression, found `{}`", lhs),
          });
        }

        if rhs.free(&lhs) {
          let rhs = Rule { map: self.compose(rhs)? };
          self.env.0.insert(
            lhs, //.
            rhs,
          );

          Ok(None)
        } else {
          Err(
            LangError::Rec, //.
          )
        }
      }

      Ast::Def(lhs, rhs) => {
        if let Expr::Fun(Function::MapExpr {
          //.
          map,
          arg,
        }) = lhs
        {
          let def = Definition { map: rhs, arg };
          self.env.1.insert(
            map, //.
            def,
          );

          Ok(None)
        } else {
          Err(LangError::Rule {
            rule: format!("definition require a functional form, found `{}`", lhs),
          })
        }
      }
    }
  }

  fn substitute_rules(&self, acc: &mut Expr, sub: &Expr) {
    if let Some(res) = self.env.0.get(sub) {
      acc.subs(sub, &res.map)
    }
  }

  fn resolve_definitions(&self, mut acc: Expr, sub: &Expr) -> Result<Expr, LangError> {
    match sub {
      Expr::Fun(Function::MapExpr {
        //.
        map,
        arg,
      }) => {
        if let Some(res) = self.env.1.get(map) {
          if arg.len() != res.arg.len() {
            return Err(LangError::Rule {
              rule: format!("function `{}` takes {} argument(s) ({} given)", map, res.arg.len(), arg.len()),
            });
          }

          let mut body = res.map.clone();
          for (arg, param) in res.arg.iter().zip(arg.iter()) {
            body.subs(arg, param)
          }

          acc.subs(&sub, &body);
          return self.compose(
            acc, //.
          );
        }
      }

      _ => {
        //.
        ()
      }
    }

    Ok(acc)
  }

  fn compose(&self, lhs: Expr) -> Result<Expr, LangError> {
    lhs.iter().fold_rec(Ok(lhs.clone()), &|acc, sub| {
      let mut acc = acc?;
      // substitute rules
      self.substitute_rules(&mut acc, sub);
      // resolve definitions
      self.resolve_definitions(
        acc, //.
        sub,
      )
    })
  }
}

pub fn parse(stmt: &str) -> Result<Expr, LangError> {
  let ast = Parser::parse(stmt, &Session { f: HashMap::new(), prev: None })?;
  if let Ast::Expr(expr) = ast {
    //
    // cf. doc
    // proof
    Ok(expr)
  } else {
    Err(LangError::Rule {
      rule: String::from("can only parse expressions, use the interpreter for other constructions"),
    })
  }
}

/// Map a Vec of expressions to a fixed number of arguments
pub fn map_args<F: Fn([Expr; E]) -> Expr, const E: usize>(f: F, arg: Vec<Expr>) -> Result<Expr, (usize, usize)> {
  let given = arg.len();
  <[Expr; E]>::try_from(arg).map_or(Err((E, given)), |arr| Ok(f(arr)))
}

pub type Span = ops::Range<usize>;

#[derive(Debug, Clone)]
pub enum LangError {
  /// Rule error
  Rule {
    //.
    rule: String,
  },

  /// Lexical error
  Lex,
  /// End error
  End,
  /// Recursive error
  Rec,

  /// Parsing integer error
  Integer { err: std::num::ParseIntError, span: Span },

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
      LangError::Rule { rule } => write!(f, "{}", rule),

      LangError::Lex => write!(f, "invalid syntax"),
      LangError::End => write!(f, "unexpected end of statement"),
      LangError::Rec => write!(f, "recursive rule detected"),

      LangError::Integer {
        //.
        err,
        span,
      } => {
        write!(
          //.
          f,
          "failed to parse integer ({}) [at {:?}]",
          err,
          span
        )
      }

      LangError::Expected {
        //.
        expr,
        span,
      } => {
        write!(
          //.
          f,
          "expected {} [at {:?}]",
          expr,
          span
        )
      }
    }
  }
}
