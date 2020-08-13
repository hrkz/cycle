pub mod parse;
pub mod token;

use std::num::ParseIntError;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
  Lexical,

  Number { err: ParseIntError, span: Range<usize> },
}
