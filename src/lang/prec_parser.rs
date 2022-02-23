use crate::lang::{Ast, Environment, Error, ErrorKind, Lexer, Semantic, Term, Token, TokenState};
use crate::*;

use std::iter::Peekable;

/// A LL(1) top-down operator precedence parser for [`Ast`] construction.
///
/// The full Cycle syntax can be specified as a context-free grammar, excluding control flow constructions.
/// We provide below its corresponding BNF specification:
///
/// ```text
/// <Primary> ::=
///    Identifier
///  | Number
///  | _
///  | <Function>
///  | "(" <Expression> ")"
///  | <Prefix> <Expression>
///
/// <Evaluation> ::= "[" <Definition> "]"
///
/// <Expression> ::=
///    <Primary> <Evaluation> <Expression>
///  | <Primary> <Notation> <Expression>
///  | <Primary>
///
/// <Definition> ::= <Expression> "=" <Expression>
///
/// <Main> ::=
///    <Definition>
///  | <Expression>
/// ```
/// The parser can handle infix and postfix operators as continuities. For prefix operators, parsing is
/// performed as literals, i.e. initiating primary expressions.
///
/// Here is the full operator table with precedence and associativity:
///
/// | Operator | Notation | Syntax  | Precedence | Associativity |
/// |----------|----------|---------|------------|---------------|
/// | Pos      | Prefix   | `+x`    | 3          | Right         |
/// | Neg      | Prefix   | `-x`    | 3          | Right         |
/// | Add      | Infix    | `x + y` | 1          | Left          |
/// | Sub      | Infix    | `x - y` | 1          | Left          |
/// | Mul      | Infix    | `x*y`   | 2          | Left          |
/// | Div      | Infix    | `x/y`   | 2          | Left          |
/// | Exp      | Infix    | `x^y`   | 4          | Right         |
/// | Fact     | Postfix  | `x!`    | 5          | Left          |
#[derive(Debug, Clone)]
pub struct Parser<'t> {
  /// The peekable (1) token stream.
  stream: Peekable<Lexer<'t>>,
  /// Context reference to the interpreting environment for substitutions.
  ctx: &'t Environment,
}

impl<'t> Parser<'t> {
  pub(crate) fn parse(
    //.
    stmt: &'t str,
    env: &'t Environment,
  ) -> Result<Ast, Error> {
    Parser {
      stream: Lexer::new(stmt).peekable(),
      ctx: env,
    }
    .main()
  }

  /// Parse a `<Main>` rule.
  pub fn main(&mut self) -> Result<Ast, Error> {
    let lhs = self.expression(0)?;

    match self.advance()? {
      Some(TokenState {
        //.
        kind: Token::Def,
        loc: _,
        src: _,
      }) => {
        let rhs = self.expression(0)?;
        Ok(Ast::Def(
          lhs, //.
          rhs,
        ))
      }

      Some(end) => Err(Error {
        kind: ErrorKind::Parsing(format!("end of statement, found remaining token `{:?}`", end.kind)),
        spot: Some(end.loc),
      }),

      None => {
        Ok(Ast::Expr(lhs)) //.
      }
    }
  }

  /// Parse an `<Expression>` rule.
  pub fn expression(&mut self, binding: u32) -> Result<Term, Error> {
    let mut lhs = self.primary()?;

    while let Some(token) = self.peek() {
      //
      // <Notation> ::=
      //    <Primary> "+" <Expression>
      //  | <Primary> "-" <Expression>
      //  | <Primary> "*" <Expression>
      //  | <Primary> "/" <Expression>
      //  | <Primary> "^"
      //  | <Primary> "!"
      //  | <Primary>

      match token {
        Token::Number | Token::Identifier | Token::LPar => {
          let state = self.bump()?;

          return Err(Error {
            kind: ErrorKind::Parsing(format!("`+, -, *, /, ^, !, [`, found `{:?}`", state.kind)),
            spot: Some(state.loc),
          });
        }

        Token::LSqr => {
          self.bump()?;
          lhs = self.evaluation(self.ctx.compose(lhs)?)?;
        }

        op => {
          match Notation::from_token(op) {
            None => {
              break; //.
            }

            Some(notation) => {
              if notation.left_prec() < binding {
                break;
              } else {
                self.bump()?;
                match notation {
                  Notation::Null(ref infix) => {
                    lhs = infix.eval(lhs, self.expression(notation.right_prec())?);
                  }

                  Notation::Right(postfix) => {
                    lhs = postfix.eval(lhs);
                  }
                }
              }
            }
          }
        }
      }
    }

    Ok(lhs)
  }

  /// Parse a `<Primary>` rule.
  pub fn primary(&mut self) -> Result<Term, Error> {
    match self.bump()? {
      TokenState {
        //.
        kind: Token::Number,
        loc,
        src,
      } => {
        let num = src
          .parse::<Natural>() // ∈ ℕ
          .map_err(|err| Error {
            kind: ErrorKind::Parsing(format!("{err:?}")),
            spot: Some(loc),
          })?;

        Ok(Tree::from(
          num, //.
        ))
      }

      TokenState {
        //.
        kind: Token::Identifier,
        loc,
        src,
      } => {
        let sym = Symbol::new(src, Number::C).ok_or(Error {
          kind: ErrorKind::Parsing(format!("valid symbol name, got `{src}`")),
          spot: Some(loc),
        })?;

        if let Some(Token::LPar) = self.peek() {
          self.bump()?;
          self.function(sym)
        } else {
          Ok(Tree::Sym(
            sym, //.
          ))
        }
      }

      TokenState {
        //.
        kind: Token::LPar,
        src: _,
        loc: _,
      } => {
        self.parenthesis() //.
      }

      TokenState { kind: Token::Pre, .. } => Ok(self.ctx.last.clone().unwrap_or(Tree::ZERO)),

      state => {
        match Prefix::from_token(state.kind) {
          Some(prefix) => {
            let rhs = self.expression(prefix.prec())?;
            Ok(prefix.eval(
              rhs, //.
            ))
          }

          None => Err(Error {
            kind: ErrorKind::Parsing(format!("`Number, Identifier, _, (, [, +, -`, found `{:?}`", state.kind)),
            spot: Some(state.loc),
          }),
        }
      }
    }
  }

  /// Parse an `<Evaluation>` rule.
  pub fn evaluation(&mut self, mut term: Term) -> Result<Term, Error> {
    let lhs = self.expression(0)?;
    match self.advance()? {
      Some(TokenState {
        //.
        kind: Token::Def,
        loc: _,
        src: _,
      }) => {
        let rhs = self.expression(0)?;
        match self.bump()? {
          TokenState {
            //.
            kind: Token::RSqr,
            loc: _,
            src: _,
          } => {
            term.subs(&lhs, &rhs);
            Ok(term)
          }

          state => Err(Error {
            kind: ErrorKind::Parsing(format!("closing bracket `]`, found `{:?}`", state.kind)),
            spot: Some(state.loc),
          }),
        }
      }

      _ => Err(Error {
        kind: ErrorKind::Parsing(format!("definition `x = y` in context evaluation (`{lhs}` given)")),
        spot: None,
      }),
    }
  }

  /// Parse a `<Function>` rule.
  pub fn function(&mut self, name: Symbol) -> Result<Term, Error> {
    // <Function> ::=
    //    Symbol "(" <List>

    let args = self.list()?;

    if let Some(f) = self.ctx.registry.get(&name) {
      f(args).map_err(|err| Error {
        kind: ErrorKind::Context(Semantic::NumArg(name, err)),
        spot: None,
      })
    } else {
      Ok(Term::map(
        name, //.
        args,
      ))
    }
  }

  /// Parse a `<List>` rule.
  pub fn list(&mut self) -> Result<List, Error> {
    // <List> ::=
    //    <Expr> <List>
    //  | "," <List>
    //  | ")"

    let expr = self.expression(0)?;
    let mut args = vec![expr];

    while let Some(Token::Comma) = self.peek() {
      self.bump()?;
      args.push(self.expression(0)?);
    }

    match self.bump()? {
      TokenState {
        //.
        kind: Token::RPar,
        loc: _,
        src: _,
      } => Ok(args),

      state => Err(Error {
        kind: ErrorKind::Parsing(format!("closing parenthesis `)`, found `{:?}`", state.kind)),
        spot: Some(state.loc),
      }),
    }
  }

  fn parenthesis(&mut self) -> Result<Term, Error> {
    let expr = self.expression(0)?;

    match self.bump()? {
      TokenState {
        //.
        kind: Token::RPar,
        loc: _,
        src: _,
      } => Ok(expr),

      state => Err(Error {
        kind: ErrorKind::Parsing(format!("closing parenthesis `)`, found `{:?}`", state.kind)),
        spot: Some(state.loc),
      }),
    }
  }

  fn advance(&mut self) -> Result<Option<TokenState>, Error> {
    self.stream.next().transpose()
  }

  /// Peek the next token without consuming it.
  pub fn peek(&mut self) -> Option<Token> {
    self.stream.peek().and_then(|result| result.as_ref().ok()).map(|token| token.kind)
  }

  /// Consume the next token with its associated state.
  pub fn bump(&mut self) -> Result<TokenState, Error> {
    self.stream.next().unwrap_or(Ok(TokenState {
      kind: Token::End, // eos
      loc: 0,
      src: "",
    }))
  }
}

type List = Vec<Tree>;

enum Prefix {
  Pos,
  Neg,
}

impl Prefix {
  fn from_token(kind: Token) -> Option<Prefix> {
    match kind {
      // `+x`
      Token::Add => Some(Prefix::Pos),
      // `-x`
      Token::Sub => Some(Prefix::Neg),
      // unrecognized token
      _ => None,
    }
  }

  fn prec(&self) -> u32 {
    match self {
      Prefix::Pos | Prefix::Neg => 3,
    }
  }

  fn eval(
    //.
    &self,
    rhs: Term,
  ) -> Term {
    match (self, rhs) {
      (Prefix::Pos, e) => e,
      (Prefix::Neg, Tree::Num(Number::Int(z))) => Tree::Num(Number::Int(-z)),
      (Prefix::Neg, e) => e.neg(),
    }
  }
}

enum Infix {
  Add,
  Sub,
  Mul,
  Div,
  Pow,
}

impl Infix {
  fn eval(
    //.
    &self,
    lhs: Term,
    rhs: Term,
  ) -> Term {
    match self {
      Infix::Add => lhs.add(rhs),
      Infix::Sub => lhs.sub(rhs),
      Infix::Mul => lhs.mul(rhs),
      Infix::Div => lhs.div(rhs),
      Infix::Pow => lhs.pow(rhs),
    }
  }
}

enum Postfix {
  Fact,
}

impl Postfix {
  fn eval(
    //.
    &self,
    lhs: Term,
  ) -> Term {
    match self {
      Postfix::Fact => lhs.fact(),
    }
  }
}

enum Associativity {
  Right,
  Left,
}

enum Notation {
  Null(Infix),
  Right(Postfix),
}

impl Notation {
  fn from_token(kind: Token) -> Option<Notation> {
    match kind {
      // `x + y`
      Token::Add => Some(Notation::Null(Infix::Add)),
      // `x - y`
      Token::Sub => Some(Notation::Null(Infix::Sub)),
      // `x*y`
      Token::Mul => Some(Notation::Null(Infix::Mul)),
      // `x/y`
      Token::Div => Some(Notation::Null(Infix::Div)),
      // `x^y`
      Token::Pow => Some(Notation::Null(Infix::Pow)),
      // `x!`
      Token::Fact => Some(Notation::Right(Postfix::Fact)),
      // unrecognized token
      _ => None,
    }
  }

  fn side(&self) -> Associativity {
    match self {
      Notation::Null(Infix::Pow) => Associativity::Right,
      Notation::Right(_) | Notation::Null(Infix::Add | Infix::Sub | Infix::Mul | Infix::Div) => Associativity::Left,
    }
  }

  fn left_prec(&self) -> u32 {
    match self {
      Notation::Null(
        Infix::Add, //.
      )
      | Notation::Null(
        Infix::Sub, //.
      ) => 1,
      Notation::Null(
        Infix::Mul, //.
      )
      | Notation::Null(
        Infix::Div, //.
      ) => 2,

      Notation::Null(
        Infix::Pow, //.
      ) => 3,
      Notation::Right(
        Postfix::Fact, //.
      ) => 4,
    }
  }

  fn right_prec(&self) -> u32 {
    let lprec = self.left_prec();
    if let Associativity::Left = self.side() {
      lprec + 1
    } else {
      lprec
    }
  }
}
