use crate::lang::{Error, ErrorKind};

use std::str::Chars;

/// The Cycle lang token.
#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub enum Token {
  /// An identifier.
  Identifier,
  /// A number (integer).
  Number,

  /// `+`
  Add,
  /// `-`
  Sub,
  /// `*`
  Mul,
  /// `/`
  Div,
  /// `^`
  Pow,
  /// `!`
  Fact,

  /// `(`
  LPar,
  /// `)`
  RPar,
  /// `[`
  LSqr,
  /// `]`
  RSqr,
  /// `,`
  Comma,
  /// `=`
  Def,
  /// `_`
  Pre,

  /// `?` keyword to request module.
  Use,
  /// Placeholder end of stream.
  End,
}

/// A token state (with linear span).
#[derive(Debug, Clone)]
pub struct TokenState<'t> {
  /// Type of token matched.
  pub kind: Token,
  /// Localization in the character stream.
  pub loc: usize,
  /// Associated slice in the character stream.
  pub src: &'t str,
}

/// A lexer iterator for [`Token`] streams.
#[derive(Debug, Clone)]
pub struct Lexer<'t> {
  /// Initial character stream.
  src: &'t str,
  /// Cursor in the character stream.
  cur: Chars<'t>,
  /// Position in the character stream.
  pos: usize,
}

impl<'t> Lexer<'t> {
  /// Create a new [`Lexer`] instance from character stream.
  pub fn new(src: &'t str) -> Lexer {
    Lexer {
      // block
      src,
      cur: src.chars(),
      pos: 0,
    }
  }

  /// Check if there is nothing more to consume.
  pub fn is_eof(&self) -> bool {
    self.cur.as_str().is_empty()
  }

  /// Peek the first next character without consuming.
  pub fn first(&self) -> Option<char> {
    self.cur.clone().next()
  }

  /// Advance to the next character.
  pub fn advance(&mut self) -> Option<usize> {
    let len = self.cur.next()?.len_utf8();
    self.pos += len;
    Some(len)
  }

  /// Advance the character stream while `predicate` is true.
  pub fn advance_while<P>(
    //.
    &mut self,
    mut predicate: P,
  ) -> Result<usize, Error>
  where
    P: FnMut(char) -> bool,
  {
    let adv = self.cur.clone().take_while(|&c| predicate(c)).try_fold(0, |len, _| Some(len + self.advance()?));

    if let Some(len) = adv {
      Ok(len)
    } else {
      Err(Error {
        kind: ErrorKind::Internal { file: file!(), line: line!() },
        spot: Some(self.pos),
      })
    }
  }

  /// Extract a [`TokenState`] for a basic (single character) [`Token`] kind.
  pub fn token(&mut self, kind: Token) -> Result<TokenState<'t>, Error> {
    let len = self.advance().ok_or(Error {
      kind: ErrorKind::Internal { file: file!(), line: line!() },
      spot: Some(self.pos),
    })?;

    Ok(self.state(
      kind, len, //.
    ))
  }

  /// Helper for [`Token::Number`] extraction.
  fn number(&mut self) -> Result<TokenState<'t>, Error> {
    let len = self.advance_while(|c| c.is_ascii_digit())?;

    Ok(self.state(
      Token::Number,
      len, //.
    ))
  }

  /// Helper for [`Token::Identifier`] extraction.
  fn identifier(&mut self) -> Result<TokenState<'t>, Error> {
    let len = self.advance_while(|c| c.is_alphabetic() || c.is_ascii_digit() || c == '_')?;

    Ok(self.state(
      Token::Identifier,
      len, //.
    ))
  }

  /// Helper for special [`Token`]s (possibly from multiple characters).
  fn special(&mut self) -> Result<TokenState<'t>, Error> {
    let len = self.advance_while(|c| !c.is_whitespace())?;
    let loc = self.pos - len;
    let src = &self.src[loc..self.pos];

    let kind = match src {
      "?" => Token::Use,

      _ => {
        return Err(Error {
          kind: ErrorKind::Lexical,
          spot: Some(loc),
        });
      }
    };

    Ok(TokenState {
      kind, //.
      loc,
      src,
    })
  }

  fn state(&self, kind: Token, len: usize) -> TokenState<'t> {
    let loc = self.pos - len;
    let src = &self.src[loc..self.pos];

    TokenState {
      kind, //.
      loc,
      src,
    }
  }
}

impl<'t> Iterator for Lexer<'t> {
  type Item = Result<TokenState<'t>, Error>;

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      return match self.first()? {
        '+' => Some(self.token(Token::Add)),
        '-' => Some(self.token(Token::Sub)),
        '*' => Some(self.token(Token::Mul)),
        '/' => Some(self.token(Token::Div)),
        '^' => Some(self.token(Token::Pow)),
        '!' => Some(self.token(Token::Fact)),

        '(' => Some(self.token(Token::LPar)),
        ')' => Some(self.token(Token::RPar)),
        '[' => Some(self.token(Token::LSqr)),
        ']' => Some(self.token(Token::RSqr)),
        ',' => Some(self.token(Token::Comma)),

        '=' => Some(self.token(Token::Def)),
        '_' => Some(self.token(Token::Pre)),

        num if num.is_ascii_digit() => Some(self.number()),
        sym if sym.is_alphabetic() => Some(self.identifier()),

        c => {
          if c.is_whitespace() {
            self.advance();
            continue;
          } else {
            Some(
              self.special(), //.
            )
          }
        }
      };
    }
  }
}
