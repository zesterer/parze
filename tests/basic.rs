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

    let bf: Parser<_, _> = recursive(|bf| (
          sym('+') - Instr::Add
        | sym('-') - Instr::Sub
        | sym('<') - Instr::Left
        | sym('>') - Instr::Right
        | sym(',') - Instr::In
        | sym('.') - Instr::Out
        | (sym('[') >> bf << sym(']')) % |ts| Instr::Loop(ts)
    ) * Any);

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
