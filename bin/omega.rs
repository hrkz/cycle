/*
 Cycle v0.1.1
 [Omega]
 Copyright (c) 2020-present, Hugo (hrkz) Frezat
*/

/// @see online
/// https://hrkz.github.io/omega/
use cycle::*;

use lang::Interpreter;

use std::env;
use std::fs;
use std::io::{self, stdin, stdout, Write};

fn main() -> io::Result<()> {
  println!("Hello Cycle! Currently ver. 0/1, or {:?}...", Number::Q(Rational::new(0, 1)).trivial());

  let mut vm = Interpreter::new(1);
  if let Some(filename) = env::args().nth(1) {
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
    match self.parse(&stmt.trim_end()) {
      // silent assignment
      Ok(None) => (),

      Ok(
        //.
        Some(expr),
      ) => {
        let expr = expr.trivial();
        expr.map_or_else(|err| eprintln!("{}", err), |expr| println!("{}", expr))
      }

      Err(err) => {
        eprintln!(
          "[error: {}] {}",
          line, // lang error
          err
        )
      }
    }
  }
}
