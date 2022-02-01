/*
 Cycle v0.3.0
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
    println!("Cycle 0.3.0 :: omega");
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

      self.interpret(1, &stmt)
    }
  }

  fn file(&mut self, filename: String) -> io::Result<()> {
    let script = fs::read_to_string(&filename)?;
    script.lines().enumerate().for_each(|(line, stmt)| self.interpret(line + 1, stmt));

    Ok(())
  }

  fn interpret(&mut self, line: usize, stmt: &str) {
    match self.run(stmt.trim_end()) {
      // variable assignment or function definition
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

struct Prelude;

impl Package for Prelude {
  fn build(&self, env: &mut Environment) -> Result<(), lang::Error> {
    self.load_elementary(env).expect(
      "failed to load elementary functions", //.
    );
    self.load_calculus(env).expect(
      "failed to load calculus operators", //.
    );
    self.load_manipulation(env).expect(
      "failed to load manipulation functions", //.
    );
    self.load_sequence(env).expect(
      "failed to load sequential operators", //.
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
    env.register_builtin(Symbol::new("Sin", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.sin()), arg) //.
    });
    env.register_builtin(Symbol::new("Cos", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.cos()), arg) //.
    });
    env.register_builtin(Symbol::new("Tan", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.tan()), arg) //.
    });

    // ```arcsin(x)```
    // ```arccos(x)```
    // ```arctan(x)```
    env.register_builtin(Symbol::new("ArcSin", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arcsin()), arg) //.
    });
    env.register_builtin(Symbol::new("ArcCos", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arccos()), arg) //.
    });
    env.register_builtin(Symbol::new("ArcTan", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arctan()), arg) //.
    });

    // ```sinh(x)```
    // ```cosh(x)```
    // ```tanh(x)```
    env.register_builtin(Symbol::new("Sinh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.sinh()), arg) //.
    });
    env.register_builtin(Symbol::new("Cosh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.cosh()), arg) //.
    });
    env.register_builtin(Symbol::new("Tanh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.tanh()), arg) //.
    });

    // ```arsinh(x)```
    // ```arcosh(x)```
    // ```artanh(x)```
    env.register_builtin(Symbol::new("ArSinh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arsinh()), arg) //.
    });
    env.register_builtin(Symbol::new("ArCosh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.arcosh()), arg) //.
    });
    env.register_builtin(Symbol::new("ArTanh", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.artanh()), arg) //.
    });

    // ```exp(x)```
    // ```log(x)```
    env.register_builtin(Symbol::new("Exp", Structure::C)?, |arg| {
      Prelude::map_fixed(|[x]| Ok(x.exp()), arg) //.
    });
    env.register_builtin(Symbol::new("Log", Structure::C)?, |arg| {
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
      let map = arg.remove(0);
      let var = arg.into_iter().map(Symbol::try_from).collect::<Symbols>();
      Ok(map.derivative(var.map_err(|_| None)?))
    });
    env.register_builtin(Symbol::new("L", Structure::C)?, |mut arg| {
      let map = arg.remove(0);
      let var = arg.into_iter().map(Symbol::try_from).collect::<Symbols>();
      Ok(map.integral(var.map_err(|_| None)?))
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
      Constant::I,
      // π ∈ R∖Q
      Constant::Pi,
      // e ∈ R∖Q
      Constant::E,
    ];

    for cte in CONSTANTS {
      env.eval(Ast::Def(Tree::Sym(Symbol::new(&format!("{:?}", cte), cte.dom()).expect("failed to declare constant")), Tree::Cte(cte)))?;
    }

    Ok(())
  }
}
