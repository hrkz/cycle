/*
 Cycle v0.2.0
 [Omega]
 Copyright (c) 2020-present, Hugo (hrkz) Frezat
*/

/// @see online
/// https://hrkz.github.io/omega/
use cycle::*;

use lang::{Ast, Interpreter, LangError};

use std::env;
use std::fs;
use std::io::{self, stdin, stdout, Write};

fn main() -> io::Result<()> {
  println!("Cycle 0.2.0 :: Omega, feb 21 2021");

  let mut vm = Interpreter::new(1);

  use_prelude(&mut vm).unwrap_or_else(|err| eprintln!("failed to load cycle prelude: {}", err));
  if let Some(filename) = env::args().nth(1) {
    vm.file(filename)
  } else {
    vm.repl()
  }
}

trait Interact {
  fn repl(&mut self) -> io::Result<()>;
  fn file(&mut self, filename: String) -> io::Result<()>;

  fn run(
    // parse statement and evaluate
    // both for
    // - repl
    // - file
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

      self.run(1, &stmt)
    }
  }

  fn file(&mut self, filename: String) -> io::Result<()> {
    let script = fs::read_to_string(filename)?;
    script.lines().enumerate().for_each(|(line, stmt)| self.run(line + 1, stmt));

    Ok(())
  }

  fn run(&mut self, line: usize, stmt: &str) {
    match self.parse(&stmt.trim_end()) {
      // rule or definition
      Ok(None) => (),

      Ok(Some(expr)) => {
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

macro_rules!
gen_prelude {
  ($vm: ident
    => $arg0: ident
      $($Def: tt),*
      &
      $($Cte: tt),*
  ) => {
    // Generate function definition
    $( $vm.eval(Ast::Def(
         Expr::map(stringify!($Def), vec!($arg0.clone())),
         Expr::$Def($arg0.clone())
       ))?;
    )*
    // Generate constant rules
    $( $vm.eval(Ast::Rule(
         Expr::Sym(Symbol::new(stringify!($Cte), Set::SR)),
         Expr::Cte(Constant::$Cte)
       ))?;
    )*
  }
}

fn use_prelude(vm: &mut Interpreter) -> Result<(), LangError> {
  let arg0 = Expr::Sym(Symbol::new("_0", Set::SR));

  gen_prelude!(
    vm => arg0

    // Trigonometric functions
    sin, arcsin,
    cos, arccos,
    tan, arctan,
    // Hyperbolic functions
    sinh, arsinh,
    cosh, arcosh,
    tanh, artanh,
    // Exponential functions
    exp, log
    &
    // Mathematical constants
    oo, pi, I
  );

  Ok(())
}
