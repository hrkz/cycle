use crate::lang::{Ast, LangError, Lexer, Token, TokenKeyword, TokenKind};
use crate::*;

use std::iter::Peekable;

///
/// LL(1) top-down operator precedence parser
///
/// ```text
/// <Primary> ::=
///    Number
///  | Symbol
///  | Keyword
///  | Symbol "(" <Expr> ")"
///  | Keyword "[" <Expr> "]" ...
///  | "(" <Expr> ")"
///  | "+" <Expr>
///  | "-" <Expr>
///
/// <Expr> ::=
///    <Primary> `operator` <Expr>
///  | <Primary>
///
/// <Root> ::=
///    <Expr> `ast` <Expr>
///  | <Expr>
/// ```
///
/// ## Operator precedence table
///
/// | Operator                  | Syntax                   | Precedence | Associativity |
/// |---------------------------|--------------------------|------------|---------------|
/// | Factorial                 | ```x!```                 | 5          | Left          |
/// | Exponentiation            | ```x^y```                | 4          | Right         |
/// | Negation                  | ```-x```                 | 3          | Left          |
/// | Multiplication / Division | ```x*y```, ```x/y```     | 2          | Left          |
/// | Addition / Substraction   | ```x + y```, ```x - y``` | 1          | Left          |
///

#[derive(Debug, Clone)]
pub struct Parser<'a> {
  tokens: Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
  pub fn parse(src: &'a str) -> Result<Ast, LangError> { Parser { tokens: Lexer::new(src).peekable() }.root() }

  fn keyword(&mut self, _keyword: TokenKeyword) -> Result<Expr, LangError> { unimplemented!() }

  fn function(&mut self, name: &str) -> Result<Expr, LangError> {
    self.next()?;
    let expr = self.expr(0)?;
    let mut arg = vec![expr];

    while let Some(TokenKind::Comma) = self.peek() {
      self.next()?;
      arg.push(self.expr(0)?);
    }

    let rpar = self.next()?;
    if let TokenKind::RPar = rpar.kind {
      Ok(Expr::map(name, arg))
    } else {
      //
      // hints
      //
      // <Primary> \in [TokenKind::RPar]
      //

      Err(LangError::Expected {
        expr: "closing parenthesis `)`, found reserved keyword",
        span: rpar.span,
      })
    }
  }

  fn parenthesis(&mut self) -> Result<Expr, LangError> {
    self.next()?;
    let expr = self.expr(0)?;
    let rpar = self.next()?;

    if let TokenKind::RPar = rpar.kind {
      Ok(expr)
    } else {
      //
      // hints
      //
      // <Primary> \in [TokenKind::RPar]
      //

      Err(LangError::Expected {
        expr: "closing parenthesis `)`, found reserved keyword",
        span: rpar.span,
      })
    }
  }

  fn primary(&mut self) -> Result<Expr, LangError> {
    match self.peek() {
      Some(TokenKind::Number(num)) => {
        self.next()?;
        Ok(Expr::Num(Number::Z(
          //.
          num.into(),
        )))
      }

      Some(TokenKind::Symbol(sym)) => {
        let sym = sym.to_string();
        self.next()?;

        if let Some(TokenKind::LPar) = self.peek() {
          self.function(
            //.
            &sym,
          )
        } else {
          Ok(Expr::Sym(Symbol::new(
            //.
            &sym,
            Set::SR,
          )))
        }
      }

      Some(TokenKind::Keyword(kw)) => {
        //.
        self.keyword(kw)
      }

      Some(TokenKind::LPar) => {
        //.
        self.parenthesis()
      }

      Some(token) => {
        if let Some(expr) = Primary::dispatch(token) {
          self.next()?;
          match expr {
            Primary::Neg | Primary::Pos => Ok(expr.eval(self.expr(expr.pred())?)),
          }
        } else {
          let token = self.next()?;

          //
          // hints
          //
          // <Primary> \in [TokenKind::Number, TokenKind::Symbol, TokenKind::LPar, TokenKind::LSqr, TokenKind::Keyword]
          // <Expr>
          //

          Err(LangError::Expected {
            expr: "`Number, Symbol, Keyword, (, [, +, -`, found non-primary operator",
            span: token.span,
          })
        }
      }

      _ => {
        //.
        self.next().and(Err(LangError::End))
      }
    }
  }

  fn expr(&mut self, binding: u32) -> Result<Expr, LangError> {
    let mut lhs = self.primary()?;

    while let Some(token) = self.peek() {
      //
      // <Expr> ::=
      //    <Primary> "+" <Expr>
      //  | <Primary> "-" <Expr>
      //  | <Primary> "*" <Expr>
      //  | <Primary> "/" <Expr>
      //  | <Primary> "^" <Expr>
      //  | <Primary> "!"
      //  | <Primary>
      //

      if let
        //.
        TokenKind::Number(_)
        | TokenKind::Symbol(_)
        | TokenKind::LPar
        | TokenKind::LSqr
        | TokenKind::Keyword(_) = token
      {
        let token = self.next()?;

        //
        // hints
        //
        // <Expr> \in [TokenKind::Add, TokenKind::Sub, TokenKind::Mul, TokenKind::Div, TokenKind::Pow, TokenKind::Fact]
        // <Expr>
        //

        return Err(LangError::Expected {
          expr: "`+, -, *, /, ^, !`, found root or primary expression",
          span: token.span,
        });
      }

      match Op::dispatch(token) {
        None => {
          break;
        }

        Some(expr) => {
          if expr.left_pred() < binding {
            break;
          } else {
            self.next()?;
            match expr {
              Op::Infix(ref i) => {
                //.
                lhs = i.eval(lhs, self.expr(expr.right_pred())?);
              }

              Op::Postfix(p) => {
                //.
                lhs = p.eval(lhs);
              }
            }
          }
        }
      }
    }

    Ok(lhs)
  }

  fn root(&mut self) -> Result<Ast, LangError> {
    //
    // <Root> ::=
    //    <Expr> ":=" <Expr>
    //  | <Expr>
    //

    let lhs = self.expr(0)?;

    match self.advance()? {
      Some(Token {
        //.
        span: _,
        kind: TokenKind::Def,
      }) => {
        let rhs = self.expr(0)?;

        if let Some(token) = self.advance()? {
          //
          // hints
          //
          // <Empty> \in []
          //

          Err(LangError::Expected {
            expr: "end of statement, found remaining token(s)",
            span: token.span,
          })
        } else {
          Ok(Ast::Define(
            //.
            lhs, rhs,
          ))
        }
      }

      Some(token) => {
        //
        // hints
        //
        // <Expr> \in [TokenKind::Def]
        // <Empty>
        //

        Err(LangError::Expected {
          expr: "`:=` or end of statement, found non-root expression",
          span: token.span,
        })
      }

      None => {
        //.
        Ok(Ast::Expr(lhs))
      }
    }
  }

  fn peek(&mut self) -> Option<TokenKind> {
    self
      .tokens
      .peek()
      // lookahead
      .and_then(|result| result.as_ref().ok())
      .map(
        |token| token.kind, //.
      )
  }

  fn next(&mut self) -> Result<Token, LangError> {
    self
      .tokens
      .next()
      // consume
      .unwrap_or(Err(LangError::End))
  }

  fn advance(&mut self) -> Result<Option<Token>, LangError> {
    self
      .tokens
      .next()
      // handle
      .transpose()
  }
}

enum Primary {
  Pos,
  Neg,
}

impl Primary {
  fn dispatch(kind: TokenKind) -> Option<Primary> {
    match kind {
      TokenKind::Add => {
        Some(Primary::Pos) // +x
      }

      TokenKind::Sub => {
        Some(Primary::Neg) // -x
      }

      _ => {
        // <Expr>
        None
      }
    }
  }

  fn pred(&self) -> u32 {
    match self {
      Primary::Pos | Primary::Neg => 3,
    }
  }

  fn eval(
    //.
    &self,
    rhs: Expr,
  ) -> Expr {
    match self {
      Primary::Pos => rhs,
      Primary::Neg => -rhs,
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
    lhs: Expr,
    rhs: Expr,
  ) -> Expr {
    match self {
      Infix::Add => lhs + rhs,
      Infix::Sub => lhs - rhs,
      Infix::Mul => lhs * rhs,
      Infix::Div => lhs / rhs,
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
    lhs: Expr,
  ) -> Expr {
    match self {
      Postfix::Fact => lhs.fact(),
    }
  }
}

enum Associativity {
  Left,
  Right,
}

enum Op {
  Infix(Infix),
  Postfix(Postfix),
}

impl Op {
  fn dispatch(kind: TokenKind) -> Option<Op> {
    match kind {
      TokenKind::Add => {
        Some(Op::Infix(Infix::Add)) // x + y
      }

      TokenKind::Sub => {
        Some(Op::Infix(Infix::Sub)) // x - y
      }

      TokenKind::Mul => {
        Some(Op::Infix(Infix::Mul)) // x*y
      }

      TokenKind::Div => {
        Some(Op::Infix(Infix::Div)) // x/y
      }

      TokenKind::Pow => {
        Some(Op::Infix(Infix::Pow)) // x^y
      }

      TokenKind::Fact => {
        Some(Op::Postfix(Postfix::Fact)) // x!
      }

      _ => {
        // <Expr>
        None
      }
    }
  }

  fn side(&self) -> Associativity {
    match self {
      Op::Infix(Infix::Pow) => Associativity::Right,
      Op::Postfix(_) | Op::Infix(Infix::Add) | Op::Infix(Infix::Sub) | Op::Infix(Infix::Mul) | Op::Infix(Infix::Div) => Associativity::Left,
    }
  }

  fn left_pred(&self) -> u32 {
    match self {
      Op::Infix(Infix::Add) | Op::Infix(Infix::Sub) => 1,
      Op::Infix(Infix::Mul) | Op::Infix(Infix::Div) => 2,
      Op::Infix(Infix::Pow) => 4,

      Op::Postfix(
        //.
        Postfix::Fact,
      ) => 5,
    }
  }

  fn right_pred(&self) -> u32 {
    if let Associativity::Left = self.side() {
      self.left_pred() + 1
    } else {
      self.left_pred()
    }
  }
}
