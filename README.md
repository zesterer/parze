# Parze

Parze is a clean, efficient parser combinator written in Rust.

## Example

A parser capable of parsing all valid Brainfuck code into an AST.

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
