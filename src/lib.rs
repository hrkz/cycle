#![feature(doc_auto_cfg)]

//!
//! Cycle is a **symbolic** mathematics library based on expression trees that focuses on correct,
//! flexible and **comprehensive** manipulation of mathematical objects. Cycle can be used to study
//! elementary and advanced mathematics, mostly in applied domains. It is in particular well suited
//! for education and research in many areas, including for example physics, astronomy, biology and
//! artificial intelligence.
//!
//! ## Important note
//!
//! * Cycle is a prototype.
//! * The API is constantly evolving and substantial changes are expected prior to stable releases (x.0.0).
//! * Feel free to suggest problems that could help to improve the library and provide realistic use cases.
//! * Help is welcomed.
//!
//! ## Mathematical objects
//!
//! Cycle gives the ability to manipulate mathematical objects. This forms the basis of a symbolic system
//! and includes the following types of expressions:
//!
//! * [`Symbol`] represents any [mathematical object](https://en.wikipedia.org/wiki/Variable_(mathematics)).
//! * [`Natural`], [`Integer`] and [`Rational`] represents [numbers](https://en.wikipedia.org/wiki/Number) in the arithmetic sense.
//! * [`Constant`] represents [mathematical constants](https://en.wikipedia.org/wiki/Mathematical_constant).
//! * [`Expr`] methods represents general [functions](https://en.wikipedia.org/wiki/Function_(mathematics)) and [operators](https://en.wikipedia.org/wiki/Operator_(mathematics)).
//!
//! Examples of practical use of these objects is demonstrated in the **tests/**.
//!
//! ## Resources
//!
//! * [Website](#)
//! * [Blog](#blog)
//! * [Usage](#usage)
//! * [Citing](#citing)
//!

#[doc(hidden)]
pub mod base;

#[cfg(feature = "cycle_lang")]
pub mod lang;

#[cfg(feature = "cycle_num")]
pub mod num;

#[cfg(feature = "cycle_plot")]
pub mod plot;

pub use crate::base::algebra::{Constant, Form, Integer, Natural, Number, Rational, SymbolicResult, Theory};
pub use crate::base::{Edge, Expr, Node, Symbol, Tree};

// Types reexport.
pub mod types {
  //! Higher order generic mathematical types.
  //!
  //! Homogeneous multidimensional array (tensor) and graph for practical use in cycle packages or user libraries.
  pub use crate::base::{
    array::{self},
    graph::{self},
  };
}
