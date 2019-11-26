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
        sym: Parser<_, _> = { '+' }

        or: Parser<_, _> = { '+' | '-' }

        then: Parser<_, _> = { '+' & '-' }

        repeat_at_least_once: Parser<_, _> = { ('+' & '-')+ }

        repeater_4: Parser<_, _> = { '+'.repeat(4) }

        mapper: Parser<_, _> = { '+' => { |c| format!("{}", c) } }

        bf: Parser<_, _> = {
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

    let foo: Parser<_, _> = rule! {
        | '0' & '1' => { |_| ('!', '?') }
        | 'a' & (('b' *= ..) => { |_| '!' })
        | 'a' & ('b' *) -> ('!', '@')
    };
}
