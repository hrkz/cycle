/*
 Cycle v0.4.1
 [Omega]
 Copyright (c) 2020-present, Hugo (hrkz) Frezat
*/

/// @see online
/// https://hrkz.github.io/omega/
use cycle::*;

use lang::{Ast, Environment, Package};

use std::io;
use std::io::Write;

use std::cmp;
use std::env;
use std::fs;

fn main() -> io::Result<()> {
  let mut env = Environment::default();

  env.register_package(Prelude).expect("failed to load cycle prelude");
  if let Some(filename) = env::args().nth(1) {
    env.file(filename)
  } else {
    println!("Cycle 0.4.1 :: omega");
    env.repl()
  }
}

trait Interact {
  fn repl(&mut self) -> io::Result<()>;
  fn file(&mut self, filename: String) -> io::Result<()>;

  fn interpret(
    // run interpreter
    // both for
    // - repl
    // - file
    &mut self,
    line: usize,
    stmt: &str,
  );
}

impl Interact for Environment {
  fn repl(&mut self) -> io::Result<()> {
    let mut stmt = String::new();

    loop {
      stmt.clear();
      print!("Ω > ");
      io::stdout().flush()?;
      io::stdin().read_line(&mut stmt)?;

      if stmt.trim_end().eq("break") {
        return Ok(());
      }

      self.interpret(
        1, //.
        &stmt,
      )
    }
  }

  fn file(&mut self, filename: String) -> io::Result<()> {
    let script = fs::read_to_string(&filename)?;
    script.lines().enumerate().for_each(|(line, stmt)| self.interpret(line + 1, stmt));

    Ok(())
  }

  fn interpret(&mut self, line: usize, stmt: &str) {
    match self.run(stmt.trim_end()) {
      // variable and function definition
      Ok(None) => (),

      Ok(Some(expr)) => {
        let expr = expr.trivial();
        expr.map_or_else(|err| eprintln!("{err}"), |expr| println!("{expr}"))
      }

      Err(err) => {
        eprintln!("[error: {line}] {err}")
      }
    }
  }
}

struct Prelude;

impl Package for Prelude {
  fn build(&self, env: &mut Environment) -> Result<(), lang::Error> {
    self.load_elementary(env);
    self.load_calculus(env);
    self.load_sequence(env);
    self.load_manipulation(env);

    self.load_constants(
      env, //.
    )
  }
}

impl Prelude {
  /// Load elementary functions.
  fn load_elementary(
    //.
    &self,
    env: &mut Environment,
  ) {
    // ```sin(x)```
    // ```cos(x)```
    // ```tan(x)```
    env.register_builtin(Symbol::new("sin", Number::C).expect("failed to declare symbol `sin`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.sin()), arg) //.
    });
    env.register_builtin(Symbol::new("cos", Number::C).expect("failed to declare symbol `cos`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.cos()), arg) //.
    });
    env.register_builtin(Symbol::new("tan", Number::C).expect("failed to declare symbol `tan`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.tan()), arg) //.
    });

    // ```arcsin(x)```
    // ```arccos(x)```
    // ```arctan(x)```
    env.register_builtin(Symbol::new("arcsin", Number::C).expect("failed to declare symbol `arcsin`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arcsin()), arg) //.
    });
    env.register_builtin(Symbol::new("arccos", Number::C).expect("failed to declare symbol `arccos`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arccos()), arg) //.
    });
    env.register_builtin(Symbol::new("arctan", Number::C).expect("failed to declare symbol `arctan`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arctan()), arg) //.
    });

    // ```sinh(x)```
    // ```cosh(x)```
    // ```tanh(x)```
    env.register_builtin(Symbol::new("sinh", Number::C).expect("failed to declare symbol `sinh`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.sinh()), arg) //.
    });
    env.register_builtin(Symbol::new("cosh", Number::C).expect("failed to declare symbol `cosh`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.cosh()), arg) //.
    });
    env.register_builtin(Symbol::new("tanh", Number::C).expect("failed to declare symbol `tanh`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.tanh()), arg) //.
    });

    // ```arsinh(x)```
    // ```arcosh(x)```
    // ```artanh(x)```
    env.register_builtin(Symbol::new("arsinh", Number::C).expect("failed to declare symbol `arsinh`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arsinh()), arg) //.
    });
    env.register_builtin(Symbol::new("arcosh", Number::C).expect("failed to declare symbol `arcosh`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arcosh()), arg) //.
    });
    env.register_builtin(Symbol::new("artanh", Number::C).expect("failed to declare symbol `artanh`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.artanh()), arg) //.
    });

    // ```exp(x)```
    // ```log(x)```
    env.register_builtin(Symbol::new("exp", Number::C).expect("failed to declare symbol `exp`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.exp()), arg) //.
    });
    env.register_builtin(Symbol::new("log", Number::C).expect("failed to declare symbol `log`"), |arg| {
      Prelude::map_fixed(|[x]| Ok(x.log()), arg) //.
    });
  }

  /// Load calculus operators.
  fn load_calculus(
    //.
    &self,
    env: &mut Environment,
  ) {
    type Symbols = Result<Vec<Symbol>, Form>;

    // ```D(x, ...) = ∂x / ∂ ... ∂```
    // ```L(x, ...) = ∫ ... ∫x d v```
    env.register_builtin(Symbol::new("D", Number::C).expect("failed to declare symbol `D`"), |mut arg| {
      Ok(arg.remove(0).derivative(arg.into_iter().map(Symbol::try_from).collect::<Symbols>().map_err(|_| None)?))
    });
    env.register_builtin(Symbol::new("L", Number::C).expect("failed to declare symbol `L`"), |mut arg| {
      Ok(arg.remove(0).integral(arg.into_iter().map(Symbol::try_from).collect::<Symbols>().map_err(|_| None)?))
    });
  }

  /// Load sequential operators.
  fn load_sequence(
    //.
    &self,
    env: &mut Environment,
  ) {
    // ```S(i, l, u, x) = x[i = l] + x[i = l + 1] + ... + x[i = u - 1] + x[i = u]```
    // ```P(i, l, u, x) = x[i = l]*x[i = l + 1]*...*x[i = u - 1]*x[i = u]```
    env.register_builtin(Symbol::new("S", Number::C).expect("failed to declare symbol `S`"), |arg| {
      Prelude::map_fixed(|[idx, lo, up, arg]| Ok(arg.sum(Symbol::try_from(idx).map_err(|_| None)?, lo, up)), arg)
    });
    env.register_builtin(Symbol::new("P", Number::C).expect("failed to declare symbol `P`"), |arg| {
      Prelude::map_fixed(|[idx, lo, up, arg]| Ok(arg.product(Symbol::try_from(idx).map_err(|_| None)?, lo, up)), arg)
    });
  }

  /// Load manipulation functions.
  fn load_manipulation(
    //.
    &self,
    env: &mut Environment,
  ) {
    env.register_builtin(Symbol::new("Expand", Number::AS).expect("failed to declare symbol `Expand`"), |arg| {
      Prelude::map_fixed(|[arg]| Ok(Tree::expand(arg).trivial().unwrap_or(Tree::Form)), arg)
    });
  }

  /// Load mathematical constants.
  fn load_constants(
    //.
    &self,
    env: &mut Environment,
  ) -> Result<(), lang::Error> {
    // Identifier `oo` for Infinity.
    env.eval(Ast::Def(
      Tree::Sym(Symbol::new("oo", Number::AS).expect("failed to declare symbol `oo`")),
      Tree::Cte(Constant::Infinity(cmp::Ordering::Greater)),
    ))?;

    const CONSTANTS: [Constant; 3] = [
      // i ∈ ℂ
      Constant::i,
      // π ∈ R∖Q
      Constant::pi,
      // e ∈ R∖Q
      Constant::e,
    ];

    for cte in CONSTANTS {
      env.eval(Ast::Def(Tree::Sym(Symbol::new(&format!("{:?}", cte), cte.dom()).expect("failed to declare constant")), Tree::Cte(cte)))?;
    }

    Ok(())
  }
}
