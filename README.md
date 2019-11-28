[![crates.io](https://img.shields.io/crates/v/parze.svg)](https://crates.io/crates/parze)
[![crates.io](https://docs.rs/parze/badge.svg)](https://docs.rs/parze)

# Parze

Parze is a clean, efficient parser combinator written in Rust.

## Example

A parser capable of parsing all valid Brainfuck code into an AST.

```rust
use parze::prelude::*;

#[derive(Clone, Debug, PartialEq)]
enum Instr { Add, Sub, Left, Right, In, Out, Loop(Vec<Instr>) }

parsers! {
    bf = {
        ( '+' -> { Instr::Add }
        | '-' -> { Instr::Sub }
        | '<' -> { Instr::Left }
        | '>' -> { Instr::Right }
        | ',' -> { Instr::In }
        | '.' -> { Instr::Out }
        | '[' -& bf &- ']' => |ts| { Instr::Loop(ts) }
        ) *
    }
}
```

## Features

- [x] All the usual parser combinator operations
- [x] Macro for simple rule and parser declaration
- [x] Support for recursive parser definitions
- [x] Custom error types - define your own!
- [x] Prioritised / merged failure for more useful errors
- [x] No dependencies - fast compilation!
- [x] `no_std` support

## Why Parze?

Parze is fast and lightweight, acting as a bare-bones framework upon which more verbose and interesting parsers can be constructed (see the `custom_error` example).

## Nightly

Parze's declaration macro currently requires a nightly Rust compiler to work.
You may use the explicit declaration form (as shown below) with stable by disabling the `nightly` feature, however.

This can be done like so in your `Cargo.toml`:

```
[dependencies.parze]
version = "x.y.z"
default-features = false
```

## Performance

Here are the results of a JSON parsing test when compared with [`pom`](https://github.com/J-F-Liu/pom). More performance metrics to come later.

```
test parze ... bench:   3,989,738 ns/iter (+/- 1,172,835)
test pom   ... bench:  22,620,632 ns/iter (+/- 5,713,893)
```

## Explicit Form

While Parze encourages use of macros for much of its declarative notation, it is possible (and often useful) to make use of the more explicit rust-y notation.

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
