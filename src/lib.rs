//!
//! Cycle - Mathematical modeling using symbolic trees
//!
//! Cycle is a symbolic mathematics and modeling library based on expression trees that
//! focuses on numerical analysis and find applications in physics, astronomy, biology,
//! artificial intelligence and many more.
//!
//! ## Motivation
//!
//! Cycle's main objective is to help researchers from different areas to design models
//! and build numerical simulations in a pleasant way, with performance and modularity.
//!
//! ## Usage
//!
//! Import `cycle` in your `Cargo.toml` file:
//!
//! ```toml
//! [dependencies]
//! cycle = "0.1.1"
//! ```
//!
//! ## Wiki
//!
//! The library is in its early stages and the wiki as well as the scientific document are
//! currently not available.
//!

#[doc(hidden)]
pub mod base;

#[cfg(feature = "cycle_lang")]
pub mod lang;

#[doc(inline)]
pub use crate::base::ring::{self, Constant, Form, Integer, Number, Rational, Set, SymbolicResult};
pub use crate::base::{Expr, Symbol};
