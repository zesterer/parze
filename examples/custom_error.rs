use parze::prelude::*;

#[derive(Debug)]
struct BrainfuckError {
    found: Option<char>,
    expected: Vec<char>, // Build up a list of expected symbols
}

impl<'a> ParseError<'a, char> for BrainfuckError {
    fn unexpected(c: char) -> Self {
        Self { found: Some(c), expected: Vec::new() }
    }

    fn unexpected_end() -> Self {
        Self { found: None, expected: Vec::new() }
    }

    fn combine(mut self, mut other: Self) -> Self {
        self.expected.append(&mut other.expected);
        self
    }
}

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

fn expect<'a>(c: char) -> Parser<'a, char, (), BrainfuckError> {
    sym(c).discard().map_err(move |mut err: BrainfuckError| {
        // Add the character to the list of expected characters if an error occurred
        err.expected.push(c);
        err
    })
}

fn main() {
    let bf: Parser<_, _, BrainfuckError> = recursive(|bf| (
          expect('+') - Instr::Add
        | expect('-') - Instr::Sub
        | expect('<') - Instr::Left
        | expect('>') - Instr::Right
        | expect(',') - Instr::In
        | ((expect('[') >> bf << expect(']')) % |ts| Instr::Loop(ts))
        | expect('.') - Instr::Out
    ) * Any);

    println!("{:?}", bf.parse("[+++".chars().collect::<Vec<_>>()));
}
