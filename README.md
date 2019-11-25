[![crates.io](https://img.shields.io/crates/v/parze.svg)](https://crates.io/crates/parze)
[![crates.io](https://docs.rs/parze/badge.svg)](https://docs.rs/parze)

# Parze

Parze is a clean, efficient parser combinator written in Rust.

## Example

A parser written with Parze that is capable of parsing all valid Brainfuck code into an AST.

```rust
use parze::prelude::*;

#[derive(Clone, Debug, PartialEq)]
enum Instr {
    Add,
    Sub,
    Left,
    Right,
    In,
    Out,
    Loop(Vec<Instr>),
}

let bf: Parser<_, _> = recursive(|bf| (
      sym('+') - Instr::Add
    | sym('-') - Instr::Sub
    | sym('<') - Instr::Left
    | sym('>') - Instr::Right
    | sym(',') - Instr::In
    | sym('.') - Instr::Out
    | (sym('[') >> bf << sym(']')) % |ts| Instr::Loop(ts)
) * Any);
```

## Why Parze?

Parze is largely a personal project. There is currently little reason to use it over a well-established existing parser combinator like [pom](https://github.com/J-F-Liu/pom).

## Explicit Form

While Parze uses operator overloading for much of its declarative notation, it is possible (and often useful) to make use of the more explicit method-based notation.

Here is the Brainfuck parser given above, declared in explicit form.

```rust
let bf: Parser<_, _> = recursive(|bf| (
        sym('+').to(Instr::Add)
    .or(sym('-').to(Instr::Sub))
    .or(sym('<').to(Instr::Left))
    .or(sym('>').to(Instr::Right))
    .or(sym(',').to(Instr::In))
    .or(sym('.').to(Instr::Out))
    .or(sym('[').delimiter_for(bf).delimited_by(sym(']')).map(|ts| Instr::Loop(ts)))
).repeat(..));
```

## License

Parze is distributed under either of:

- Apache License, Version 2.0, (LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0)

- MIT license (LICENSE-MIT or http://opensource.org/licenses/MIT)

at the disgression of the user.
