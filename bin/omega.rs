/*
 Cycle v0.4.0
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
    println!("Cycle 0.4.0 :: omega");
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
    self
      .load_elementary(env)
      .and(self.load_calculus(env))
      .and(self.load_sequence(env))
      .and(self.load_manipulation(env))
      .expect(
        "failed to load basic packages", //.
      );

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
  ) -> Option<()> {
    // ```sin(x)```
    // ```cos(x)```
    // ```tan(x)```
    env.register_builtin(Symbol::new("sin", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.sin()), arg) //.
    });
    env.register_builtin(Symbol::new("cos", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.cos()), arg) //.
    });
    env.register_builtin(Symbol::new("tan", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.tan()), arg) //.
    });

    // ```arcsin(x)```
    // ```arccos(x)```
    // ```arctan(x)```
    env.register_builtin(Symbol::new("arcsin", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arcsin()), arg) //.
    });
    env.register_builtin(Symbol::new("arccos", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arccos()), arg) //.
    });
    env.register_builtin(Symbol::new("arctan", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arctan()), arg) //.
    });

    // ```sinh(x)```
    // ```cosh(x)```
    // ```tanh(x)```
    env.register_builtin(Symbol::new("sinh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.sinh()), arg) //.
    });
    env.register_builtin(Symbol::new("cosh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.cosh()), arg) //.
    });
    env.register_builtin(Symbol::new("tanh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.tanh()), arg) //.
    });

    // ```arsinh(x)```
    // ```arcosh(x)```
    // ```artanh(x)```
    env.register_builtin(Symbol::new("arsinh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arsinh()), arg) //.
    });
    env.register_builtin(Symbol::new("arcosh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arcosh()), arg) //.
    });
    env.register_builtin(Symbol::new("artanh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.artanh()), arg) //.
    });

    // ```exp(x)```
    // ```log(x)```
    env.register_builtin(Symbol::new("exp", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.exp()), arg) //.
    });
    env.register_builtin(Symbol::new("log", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.log()), arg) //.
    });

    Some(())
  }

  /// Load calculus operators.
  fn load_calculus(
    //.
    &self,
    env: &mut Environment,
  ) -> Option<()> {
    type Symbols = Result<Vec<Symbol>, Form>;

    // ```D(x, ...) = ∂x / ∂ ... ∂```
    // ```L(x, ...) = ∫ ... ∫x d v```
    env.register_builtin(Symbol::new("D", Structure::C)?, |mut arg| {
      Ok(arg.remove(0).derivative(arg.into_iter().map(Symbol::try_from).collect::<Symbols>().map_err(|_| None)?))
    });
    env.register_builtin(Symbol::new("L", Structure::C)?, |mut arg| {
      Ok(arg.remove(0).integral(arg.into_iter().map(Symbol::try_from).collect::<Symbols>().map_err(|_| None)?))
    });

    Some(())
  }

  /// Load sequential operators.
  fn load_sequence(
    //.
    &self,
    env: &mut Environment,
  ) -> Option<()> {
    // ```S(i, l, u, x) = x[i = l] + x[i = l + 1] + ... + x[i = u - 1] + x[i = u]```
    // ```P(i, l, u, x) = x[i = l]*x[i = l + 1]*...*x[i = u - 1]*x[i = u]```
    env.register_builtin(Symbol::new("S", Structure::C)?, |arg| {
      Prelude::map_fixed(|[idx, lo, up, arg]| Ok(arg.sum(Symbol::try_from(idx).map_err(|_| None)?, lo, up)), arg)
    });
    env.register_builtin(Symbol::new("P", Structure::C)?, |arg| {
      Prelude::map_fixed(|[idx, lo, up, arg]| Ok(arg.product(Symbol::try_from(idx).map_err(|_| None)?, lo, up)), arg)
    });

    Some(())
  }

  /// Load manipulation functions.
  fn load_manipulation(
    //.
    &self,
    env: &mut Environment,
  ) -> Option<()> {
    env.register_builtin(Symbol::new("Expand", Structure::AS)?, |arg| {
      Prelude::map_fixed(|[arg]| Ok(Tree::expand(arg).trivial().unwrap_or(Tree::Form)), arg)
    });

    Some(())
  }

  /// Load mathematical constants.
  fn load_constants(
    //.
    &self,
    env: &mut Environment,
  ) -> Result<(), lang::Error> {
    // Identifier `oo` for Infinity.
    env.eval(Ast::Def(
      Tree::Sym(Symbol::new("oo", Structure::AS).expect("failed to declare Infinity")),
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
