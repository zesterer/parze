use parze::prelude::*;

#[test]
fn brainfuck() {
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

    parsers! {
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

    let program_src = "++++[->++++<]>[->++++<]>.";

    let program_tgt = vec![ // Prints '@'
        Instr::Add,
        Instr::Add,
        Instr::Add,
        Instr::Add,
        Instr::Loop(vec![
            Instr::Sub,
            Instr::Right,
            Instr::Add,
            Instr::Add,
            Instr::Add,
            Instr::Add,
            Instr::Left,
        ]),
        Instr::Right,
        Instr::Loop(vec![
            Instr::Sub,
            Instr::Right,
            Instr::Add,
            Instr::Add,
            Instr::Add,
            Instr::Add,
            Instr::Left,
        ]),
        Instr::Right,
        Instr::Out,
    ];

    assert_eq!(bf.parse(program_src.chars().collect::<Vec<_>>()), Ok(program_tgt));
}
