/*
 Cycle v0.2.1
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
  let mut vm = Interpreter::new(1);

  Prelude::new().use_into(&mut vm, true).unwrap_or_else(|err| eprintln!("failed to load cycle prelude: {}", err));
  if let Some(filename) = env::args().nth(1) {
    vm.file(filename)
  } else {
    println!("Cycle 0.2.1 :: Omega, feb 23 2021");
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

///
/// Mathematical constants >
/// oo, pi, I
///
/// Arithmetic functions >
/// +, -, *, /, ^, !, sqrt
///
/// Elementary functions >
/// sin, cos, tan, arcsin, arccos, arctan, sinh, cosh, tanh, arsinh, arcosh, artanh, log, exp
///
struct Prelude {
  arg: Expr,
}

impl Prelude {
  fn new() -> Prelude {
    Prelude {
      arg: Expr::Sym(Symbol::new("_0", Set::SR)),
    }
  }

  fn def<F>(
    //.
    &self,
    vm: &mut Interpreter,
    name: &str,
    f: F,
  ) -> Result<Option<Expr>, LangError>
  where
    F: Fn(Expr) -> Expr,
  {
    let _0 = self.arg.clone();
    vm.eval(Ast::Def(Expr::map(name, vec![_0.clone()]), f(_0)))
  }

  fn use_into(
    //.
    &self,
    vm: &mut Interpreter,
    _op: bool,
  ) -> Result<(), LangError> {
    self.def(vm, "sqrt", |e| e.sqrt())?;

    self.def(vm, "sin", |e| e.sin())?;
    self.def(vm, "cos", |e| e.cos())?;
    self.def(vm, "tan", |e| e.tan())?;

    self.def(vm, "arcsin", |e| e.arcsin())?;
    self.def(vm, "arccos", |e| e.arccos())?;
    self.def(vm, "arctan", |e| e.arctan())?;

    self.def(vm, "sinh", |e| e.sinh())?;
    self.def(vm, "cosh", |e| e.cosh())?;
    self.def(vm, "tanh", |e| e.tanh())?;

    self.def(vm, "arsinh", |e| e.arsinh())?;
    self.def(vm, "arcosh", |e| e.arcosh())?;
    self.def(vm, "artanh", |e| e.artanh())?;

    self.def(vm, "exp", |e| e.exp())?;
    self.def(vm, "log", |e| e.log())?;

    vm.eval(Ast::Rule(Expr::Sym(Symbol::new("oo", Set::SR)), Expr::Cte(Constant::oo)))?;
    vm.eval(Ast::Rule(Expr::Sym(Symbol::new("pi", Set::SR)), Expr::Cte(Constant::pi)))?;
    vm.eval(Ast::Rule(Expr::Sym(Symbol::new("I", Set::SR)), Expr::Cte(Constant::I)))?;

    Ok(())
  }
}
