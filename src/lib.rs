//!
//! Cycle is a **symbolic** mathematics library based on expression trees that focuses on correct,
//! flexible and **comprehensive** manipulation of mathematical objects. Cycle can be used to study
//! elementary and advanced mathematics, mostly in applied domains. It is in particular well suited
//! for education and research in many areas, including for example physics, astronomy, biology and
//! artificial intelligence.
//!
//! ## Usage
//!
//! To use cycle, you will need a modern [Rust](https://www.rust-lang.org/) version with [Cargo](https://doc.rust-lang.org/stable/cargo/)
//! for the compilation and testing,
//!
//! ```toml
//! [dependencies]
//! cycle = "0.2.1"
//! ```
//!
//! ## Getting started
//!
//! An extensive tutorial is currently under construction, but you can read the [online documentation](https://docs.rs/cycle)
//! for the latest release. Note that the library is still in an early phase and API changes are expected.
//!
//! ## Citing
//!
//! We acknowledge the importance of reproducible research, in particular through open-access software. If you used Cycle, we ask that you cite the project in your work.
//!

#[doc(hidden)]
pub mod base;

#[cfg(feature = "cycle_lang")]
pub mod lang;

#[cfg(feature = "cycle_plot")]
pub mod plot;

pub use crate::base::ring::{self, Constant, Form, Integer, Number, Rational, Set, SymbolicResult};
pub use crate::base::{Expr, Symbol};

pub use crate::base::fun::{Function, Special};

/// Abstract data types
pub mod types {
  //! ## Require some description
  pub use crate::base::{
    array::{
      //.
      self,
      Array,
      ArrayBase,
    },
    graph::{
      //.
      self,
      GraphBase,
    },
  };
}
