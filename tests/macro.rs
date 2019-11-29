#![feature(proc_macro_hygiene)]

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

#[test]
#[allow(unused_variables)]
fn simple() {
    parsers! {
        sym: Parser<char, _> = { '+' }

        or: Parser<char, _> = { '+' | '-' }

        then: Parser<char, _> = { '+' & '-' }

        repeat_at_least_once: Parser<char, _> = { ('+' & '-')+ }

        repeater_4: Parser<char, _> = { '+'* }

        mapper: Parser<char, _> = { '+' => { |c| format!("{}", c) } }

        bf: Parser<char, _> = {
            ( '+' -> { Instr::Add }
            | '-' -> { Instr::Sub }
            | '<' -> { Instr::Left }
            | '>' -> { Instr::Right }
            | ',' -> { Instr::In }
            | '.' -> { Instr::Out }
            | '[' -& bf &- ']' => { |i| Instr::Loop(i) }
            )*
        }
    }

    bf.parse(&"++[,>>]++-".chars().collect::<Vec<_>>()).unwrap();
}
