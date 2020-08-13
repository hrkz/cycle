/*
 Cycle v0.0.4
 [main]
 Copyright (c) 2020-present, Hugo (hrkz) Frezat
*/

/// @see wiki
/// http://cycle-research.org
use cycle::*;

use lang::token::Lexer;

use std::env;
use std::fs;
use std::io::{self, stdin, stdout, Write};

fn main() -> io::Result<()> {
  println!("Hello Cycle! Currently ver. 0/4, or {:?}...", Number::Q(Rational::new(0, 4)).trivial());

  let mut vm = Interpreter {};
  if let Some(filename) = env::args().skip(1).next() {
    vm.run_script(filename)
  } else {
    vm.repl()
  }
}

struct Interpreter {}

impl Interpreter {
  fn print_tokens(&self, statement: &str) { Lexer::new(statement).for_each(|token| println!("{:?}", token)) }

  fn repl(&mut self) -> io::Result<()> {
    let mut buffer = String::new();

    loop {
      buffer.clear();
      print!("Γ > ");
      stdout().flush()?;
      stdin().read_line(&mut buffer)?;

      self.print_tokens(
        //.
        &buffer,
      );
    }
  }

  fn run_script(&self, filename: String) -> io::Result<()> {
    let script = fs::read_to_string(filename)?;
    script
      //.
      .lines()
      .for_each(|line| {
        self.print_tokens(
          //.
          &line,
        );
      });

    Ok(())
  }
}
