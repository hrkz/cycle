Cycle: modern and safe symbolic mathematics
===

[![Build](https://img.shields.io/github/workflow/status/hrkz/cycle/CI?style=flat-square)](https://github.com/hrkz/cycle/actions)
[![Crate](https://img.shields.io/crates/v/cycle?style=flat-square)](https://crates.io/crates/cycle)
[![License](https://img.shields.io/github/license/hrkz/cycle.svg?color=informational&style=flat-square)](https://github.com/hrkz/cycle/blob/master/LICENSE)
[![Milestones](https://img.shields.io/github/milestones/open/hrkz/cycle?label=milestones&style=flat-square)](https://github.com/hrkz/cycle/milestones)

### Table of contents

* [Website](#)
* [Usage](#usage)
* [Getting started](#getting-started)
* [Citing](#citing)

Cycle is a **symbolic** mathematics library based on expression trees that focuses on correct, flexible and **comprehensive** manipulation of mathematical objects. Cycle can be used to study elementary and advanced mathematics, mostly in applied domains. It is in particular well suited for education and research in many areas, including for example physics, astronomy, biology and artificial intelligence.

#### Try the [online notebook](https://hrkz.github.io/omega/) running on WebAssembly.

## Usage

To use cycle, you will need [Git](https://git-scm.com/) for cloning and a modern [Rust](https://www.rust-lang.org/) version with [Cargo](https://doc.rust-lang.org/stable/cargo/) for the compilation and testing,
```bash
# Clone the repository
$ git clone https://github.com/hrkz/cycle && cd cycle

# Start the compilation and download dependencies
$ cargo build
$ cargo test # Run the tests (optional)
$ cargo run # Run the interpreter (optional)
```
or with the crate
```toml
[dependencies]
cycle = "0.2.1"
```

## Getting started

An extensive tutorial is currently under construction, but you can read the [online documentation](https://docs.rs/cycle) for the latest release. Note that the library is still in an early phase and API changes are expected.

## Citing

We acknowledge the importance of reproducible research, in particular through open-access software. If you used Cycle, we ask that you cite the project in your work. 
