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
  let mut vm = Interpreter::new();

  Prelude::new().load(&mut vm).unwrap_or_else(|err| eprintln!("failed to load cycle prelude: {}", err));
  if let Some(filename) = env::args().nth(1) {
    vm.file(filename)
  } else {
    println!("Cycle 0.2.1 :: omega");
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

struct Prelude {}

impl Prelude {
  fn new() -> Self { Prelude {} }

  ///
  /// Elementary functions >
  /// sin, cos, tan, arcsin, arccos, arctan, sinh, cosh, tanh, arsinh, arcosh, artanh, log, exp
  ///
  fn load_elementary(&mut self, vm: &mut Interpreter) -> Result<(), LangError> {
    // ```sin(x)```
    // ```cos(x)```
    // ```tan(x)```
    vm.bind_function("sin", |arg| {
      lang::map_args(|[x]| x.sin(), arg) //.
    });
    vm.bind_function("cos", |arg| {
      lang::map_args(|[x]| x.cos(), arg) //.
    });
    vm.bind_function("tan", |arg| {
      lang::map_args(|[x]| x.tan(), arg) //.
    });

    // ```arcsin(x)```
    // ```arccos(x)```
    // ```arctan(x)```
    vm.bind_function("arcsin", |arg| {
      lang::map_args(|[x]| x.arcsin(), arg) //.
    });
    vm.bind_function("arccos", |arg| {
      lang::map_args(|[x]| x.arccos(), arg) //.
    });
    vm.bind_function("arctan", |arg| {
      lang::map_args(|[x]| x.arctan(), arg) //.
    });

    // ```sinh(x)```
    // ```cosh(x)```
    // ```tanh(x)```
    vm.bind_function("sinh", |arg| {
      lang::map_args(|[x]| x.sinh(), arg) //.
    });
    vm.bind_function("cosh", |arg| {
      lang::map_args(|[x]| x.cosh(), arg) //.
    });
    vm.bind_function("tanh", |arg| {
      lang::map_args(|[x]| x.tanh(), arg) //.
    });

    // ```arsinh(x)```
    // ```arcosh(x)```
    // ```artanh(x)```
    vm.bind_function("arsinh", |arg| {
      lang::map_args(|[x]| x.arsinh(), arg) //.
    });
    vm.bind_function("arcosh", |arg| {
      lang::map_args(|[x]| x.arcosh(), arg) //.
    });
    vm.bind_function("artanh", |arg| {
      lang::map_args(|[x]| x.artanh(), arg) //.
    });

    // ```exp(x)```
    // ```log(x)```
    vm.bind_function("exp", |arg| {
      lang::map_args(|[x]| x.exp(), arg) //.
    });
    vm.bind_function("log", |arg| {
      lang::map_args(|[x]| x.log(), arg) //.
    });

    Ok(())
  }

  ///
  /// Calculus operators >
  /// differentiation (D), integration (L)
  ///
  fn load_calculus(&mut self, vm: &mut Interpreter) -> Result<(), LangError> {
    // ```D(x, ...) = ∂x / ∂ ... ∂```
    vm.bind_function("D", |mut arg| {
      Ok(arg.remove(0).derivative(arg)) //.
    });
    // ```L(x, ...) = ∫ ... ∫x d v```
    vm.bind_function("L", |mut arg| {
      Ok(arg.remove(0).integral(arg)) //.
    });

    Ok(())
  }

  ///
  /// Mathematical constants >
  /// oo, pi, I
  ///
  fn load_constants(&mut self, vm: &mut Interpreter) -> Result<(), LangError> {
    vm.eval(Ast::Rule(Expr::Sym(Symbol::new("oo", Set::SR)), Expr::Cte(Constant::Infinity(1))))?;
    vm.eval(Ast::Rule(Expr::Sym(Symbol::new("pi", Set::SR)), Expr::Cte(Constant::pi)))?;
    vm.eval(Ast::Rule(Expr::Sym(Symbol::new("i", Set::SR)), Expr::Cte(Constant::i)))?;

    Ok(())
  }

  fn load(&mut self, vm: &mut Interpreter) -> Result<(), LangError> {
    self.load_elementary(vm)?;
    self.load_calculus(vm)?;
    self.load_constants(vm)?;

    Ok(())
  }
}
