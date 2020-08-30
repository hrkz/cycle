/*
 Cycle v0.1.0
 [main]
 Copyright (c) 2020-present, Hugo (hrkz) Frezat
*/

/// @see book
/// http://cycle-research.org
use cycle::*;

use lang::Interpreter;

use std::env;
use std::fs;
use std::io::{self, stdin, stdout, Write};

fn main() -> io::Result<()> {
  println!("Hello Cycle! Currently ver. 0/1, or {:?}...", Number::Q(Rational::new(0, 1)).trivial());

  let mut vm = Interpreter::new(1);
  if let Some(filename) = env::args().skip(1).next() {
    vm.file(filename)
  } else {
    vm.repl()
  }
}

trait Interact {
  fn repl(&mut self) -> io::Result<()>;

  fn file(&mut self, filename: String) -> io::Result<()>;

  /// Parse statement
  /// and run action on resulting expr
  fn interpret(
    //.
    &mut self,
    line: usize,
    stmt: &str,
  );
}

impl Interact for Interpreter {
  fn repl(&mut self) -> io::Result<()> {
    let mut stmt = String::new();

    loop {
      stmt.clear();
      print!("Ω > ");
      stdout().flush()?;
      stdin().read_line(&mut stmt)?;

      self.interpret(1, &stmt)
    }
  }

  fn file(&mut self, filename: String) -> io::Result<()> {
    let script = fs::read_to_string(filename)?;
    script.lines().enumerate().for_each(|(line, stmt)| self.interpret(line + 1, stmt));

    Ok(())
  }

  fn interpret(&mut self, line: usize, stmt: &str) {
    match self.eval(&stmt.trim_end()) {
      // silent assignment
      Ok(None) => (),

      Ok(
        //.
        Some(expr),
      ) => {
        // print expr
        println!("{}", expr)
      }

      Err(err) => {
        // lang error
        eprintln!("[error: {}] {}", line, err)
      }
    }
  }
}
