<div align="center">

[![Cycle](https://raw.githubusercontent.com/hrkz/cycle/gh-pages/images/cycle_logo.png)](https://cycle-research.org)

[![Build](https://img.shields.io/github/workflow/status/hrkz/cycle/CI?style=flat-square)](https://github.com/hrkz/cycle/actions)
[![Crate](https://img.shields.io/crates/v/cycle?style=flat-square)](https://crates.io/crates/cycle)
[![License](https://img.shields.io/github/license/hrkz/cycle.svg?color=informational&style=flat-square)](https://github.com/hrkz/cycle/blob/master/LICENSE)
[![Milestones](https://img.shields.io/github/milestones/open/hrkz/cycle?label=milestones&style=flat-square)](https://github.com/hrkz/cycle/milestones)

</div>
<hr>

### Table of contents

* [Website](https://cycle-research.org)
* [Features](https://cycle-research.org/features)
* [Getting started](#getting-started)
* [Papers](https://scholar.google.com/scholar?cites=0)
* [Contact](https://hrkz.github.io)

Cycle is a *symbolic* mathematics and modeling library based on expression trees that focuses on *numerical analysis*
and find applications in physics, astronomy, biology, artificial intelligence and many more.

##### Research driven

Cycle's main objective is to help researchers from different areas to design models and build numerical
simulations in a pleasant way, with performance and modularity.

## Getting started

To use cycle, you will need [Git](https://git-scm.com/) for cloning and a modern [Rust](https://www.rust-lang.org/) version with [Cargo](https://doc.rust-lang.org/stable/cargo/) for the compilation and testing,
```bash
# Clone the repository
$ git clone https://github.com/hrkz/cycle && cd cycle

# Start the compilation and download dependencies
$ cargo build
$ cargo test # Run tests (optional)
$ cargo run # Run the interpreter (optional)
```
or with the crate
```toml
[dependencies]
cycle = "0.0.2"
```

| Plans |       |
| :----:| :----:|
| :book: [book](https://github.com/hrkz/cycle/wiki) \| [docs](https://docs.rs/crate/cycle/0.0.2) | To get started with the library, learn the basics through the book, reference documentation and examples |
