#![feature(proc_macro_hygiene)]

use parze::prelude::*;
use parze_declare::*;

#[test]
fn basic() {
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

    let bf: Parser<_, _> = recursive(|bf| rule! {
        (
        | '+' -> { Instr::Add }
        | '-' -> { Instr::Sub }
        | '<' -> { Instr::Left }
        | '>' -> { Instr::Right }
        | ',' -> { Instr::In }
        | '.' -> { Instr::Out }
        | '[' -& bf &- ']' => { |i| Instr::Loop(i) }
        )*
    });

    assert_eq!(
        bf.parse("[-]++++[->++++<][->++++<][->++++<].".chars().collect::<Vec<_>>()),
        Ok(vec![Instr::Add])
    );
}
