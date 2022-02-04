//! Parsing, validation and generation of mathematical expressions.

mod codegen_jit;
mod lexer;
mod prec_parser;

pub use lexer::{Lexer, Token, TokenState};
pub use prec_parser::Parser;

use crate::{base::Function, Symbol, Tree};

use std::any;
use std::collections::HashMap;
use std::error;
use std::fmt;

/// An [`Ast`] term, currently referring to n [`Tree`].
pub type Term = Tree;

/// The complete AST (Abstract Syntax Tree) for a Cycle lang script.
///
/// The reference is described mainly as a mathematical language with special operators.
///
/// # Capabilities
///
/// Here is a simple list of basic language constructions:
/// - Expression evaluation `x`.
/// - Variable declaration `v = x`.
/// - Function definition `f(a1, ..., an) = ...`.
/// - Context evaluation `(x1 ... xn)[x1 = y1] ... [xn = yn]`.
///
/// # Examples
///
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Ast {
  Expr(Term),

  /// `v = x` or `f(a_) = ...`
  Def(Term, Term),
  //
  // Modules
  // (Use)
  //
}

/// A function construction return type.
pub type Construction = Option<(usize, usize)>;

/// A function definition.
#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionMap {
  /// Function expression (rhs).
  map: Term,
  /// Function arguments (lhs).
  arg: Vec<Tree>,
}

/// Builtin function type.
type Builtin = fn(Vec<Tree>) -> Result<Term, Construction>;

/// The Cycle lang execution environment.
///
/// Store variables and function definitions, but could potentially support more, such as modules.
/// Last executed command (or script) is accessible through alias `_`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Environment {
  /// Version.
  version: u16,
  /// Builtin registry.
  registry: HashMap<Symbol, Builtin>,
  /// Variables storage.
  variables: HashMap<Tree, Term>,
  /// Functions storage.
  functions: HashMap<Symbol, FunctionMap>,
  /// Last executed command.
  last: Option<Term>,
}

impl Environment {
  /// Run interpreting steps (parsing and evaluation) from a statement into a [`Term`].
  pub fn run(&mut self, stmt: &str) -> Result<Option<Term>, Error> {
    if stmt.is_empty() {
      return Ok(None);
    }

    let ast = self.parse(stmt)?;
    self.eval(
      ast, //.
    )
  }

  /// Parse a statement (character stream) into a resulting [`Ast`].
  pub fn parse(&mut self, stmt: &str) -> Result<Ast, Error> {
    Parser::parse(
      stmt, //.
      self,
    )
  }

  /// Evaluate (interpret) an [`Ast`] into a [`Term`], applying corresponding modifications to the [`Environment`].
  pub fn eval(&mut self, ast: Ast) -> Result<Option<Term>, Error> {
    match ast {
      Ast::Expr(expr) => {
        // lookup
        Ok(Some(self.last.insert(self.compose(expr)?).clone()))
      }

      Ast::Def(lhs, rhs) => {
        match lhs {
          Tree::Num(_) | Tree::Cte(_) => {
            return Err(Error {
              kind: ErrorKind::Context(Semantic::CteDef(lhs)), //.
              spot: None,
            });
          }

          Tree::Fun(Function::MapExpr { map, arg }) if self.functions.get(&map).is_none() => {
            let rhs = FunctionMap { map: rhs, arg: arg.to_vec() };
            self.functions.insert(
              map, //.
              rhs,
            );
          }

          lhs => {
            let rhs = self.compose(rhs)?;
            self.variables.insert(
              lhs, //.
              rhs,
            );
          }
        }

        Ok(None)
      }
    }
  }

  /// Register a builtin function in the environment.
  pub fn register_builtin(
    //.
    &mut self,
    name: Symbol,
    f: Builtin,
  ) {
    self.registry.insert(name, f);
  }

  /// Register a package in the environment.
  pub fn register_package<P>(
    //.
    &mut self,
    package: P,
  ) -> Result<&mut Self, Error>
  where
    P: Package,
  {
    package.build(self)?;
    Ok(self)
  }

  fn substitute_variable(&self, acc: &mut Term, sub: &Tree) {
    if let Some(res) = self.variables.get(sub) {
      acc.subs(sub, res);
    }
  }

  fn resolve_function(&self, mut acc: Term, sub: &Tree) -> Result<Term, Error> {
    if let Tree::Fun(Function::MapExpr { map, arg }) = sub {
      if let Some(res) = self.functions.get(map) {
        if arg.len() != res.arg.len() {
          return Err(Error {
            kind: ErrorKind::Context(Semantic::NumArg(map.clone(), Some((res.arg.len(), arg.len())))), //.
            spot: None,
          });
        }

        let mut body = res.map.clone();
        for (arg, param) in res.arg.iter().zip(arg.iter()) {
          body.subs(arg, param);
        }

        acc.subs(sub, &body);
        return self.compose(
          acc, //.
        );
      }
    }

    Ok(acc)
  }

  fn compose(&self, lhs: Term) -> Result<Term, Error> {
    lhs.iter().fold_rec(Ok(lhs.clone()), &|acc, sub| {
      let mut acc = acc?;
      // substitute variable
      self.substitute_variable(&mut acc, sub);
      // resolve function
      self.resolve_function(
        acc, //.
        sub,
      )
    })
  }
}

/// Parse a single expression without creating a dedicated [`Environment`].
pub fn parse(stmt: &str) -> Result<Term, Error> {
  let (Ast::Expr(rhs) | Ast::Def(_, rhs)) = Parser::parse(stmt, &Environment::default())?;
  Ok(rhs)
}

/// A package trait that extends [`Environment`] functionalities.
pub trait Package {
  /// Build package features into the [`Environment`].
  fn build(&self, env: &mut Environment) -> Result<(), Error>;
  /// Retrieve package name.
  fn name(&self) -> &str {
    any::type_name::<Self>()
  }

  /// Try to map a list of [`Tree`] to a fixed number of elements.
  fn map_fixed<F: Fn([Tree; N]) -> Result<Term, Construction>, const N: usize>(
    //.
    f: F,
    v: Vec<Tree>,
  ) -> Result<Term, Construction> {
    let m = v.len();
    <[Tree; N]>::try_from(v).map_or(
      Err(Some((
        N, //.
        m,
      ))),
      f,
    )
  }
}

/// A list of semantic rules.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Semantic {
  /// A constant or number on declaration's lhs.
  CteDef(Term),
  /// Invalid function arguments.
  NumArg(Symbol, Construction),
}

/// A list of general lang errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
  /// A lexical error.
  Lexical,
  /// A parsing error from invalid token.
  Parsing(String),
  /// A context error during evaluation.
  Context(Semantic),
  /// An internal error.
  Internal {
    //.
    file: &'static str,
    line: u32,
  },
}

/// An error that occurs during interpreting phases (lex, parse or eval).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
  kind: ErrorKind,
  spot: Option<usize>,
}

impl error::Error for Error {}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self.kind {
      ErrorKind::Lexical => write!(f, "invalid syntax"),
      ErrorKind::Parsing(message) => write!(f, "expected {message}"),
      ErrorKind::Context(feature) => feature.fmt(f),
      ErrorKind::Internal { file, line } => write!(f, "internal error in [{file}:{line}]"),
    }?;

    if let Some(spot) = &self.spot {
      write!(f, " at ({spot:?})")?;
    }

    Ok(())
  }
}

impl fmt::Display for Semantic {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Semantic::CteDef(lhs) => write!(f, "definition requires a non-constant expression, found `{lhs}` on lhs"),
      Semantic::NumArg(map, Some((arg, given))) => write!(f, "function `{map}` takes {arg} argument(s) ({given} given)"),
      Semantic::NumArg(map, None) => write!(f, "function `{map}` received invalid argument(s) type(s)"),
    }
  }
}
