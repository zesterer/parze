use parze::prelude::*;
use std::collections::HashSet;

type Token = (usize, char);

#[derive(Debug)]
struct BrainfuckError {
    found: Option<Token>,
    expected: HashSet<char>, // A list of expected symbols, assembled during error propagation
}

impl BrainfuckError {
    // This is pretty poor code, you can do better
    fn print(&self, code: &str) {
        println!("1 | {}", code);

        if let Some((idx, _)) = self.found {
            print!("  | ");
            for _ in 0..idx {
                print!(" ");
            }
            println!("^");
        }

        let expected_str = self.expected
            .iter()
            .map(|c| format!("'{}'", c))
            .collect::<Vec<_>>()
            .join(", ");
        match self.found {
            Some((idx, c)) => println!("Error at column {}: Found '{}', expected one of {}", idx + 1, c, expected_str),
            None => println!("Error at end of line: Expected one of {}", expected_str),
        }
    }
}

impl<'a> ParseError<'a, Token> for BrainfuckError {
    fn unexpected(token: Token) -> Self {
        Self { found: Some(token), expected: HashSet::default() }
    }

    fn unexpected_end() -> Self {
        Self { found: None, expected: HashSet::default() }
    }

    // Combine two same-priority errors together
    fn combine(mut self, other: Self) -> Self {
        self.expected = self.expected
            .union(&other.expected)
            .copied()
            .collect();
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

// A parser that only accepts tokens with matching characters and produces an "Expected 'c'" error
fn expect<'a>(c: char) -> Parser<'a, Token, (), BrainfuckError> {
    permit(move |(_, found_c)| found_c == c)
        .discard()
        .map_err(move |mut err: BrainfuckError| {
            // Add the character to the list of expected characters if an error occurred
            err.expected.insert(c);
            err
        })
}

fn main() {
    parsers! {
        bf: Parser<_, _, BrainfuckError> = {
            ( { expect('+') } -> { Instr::Add }
            | { expect('-') } -> { Instr::Sub }
            | { expect('<') } -> { Instr::Left }
            | { expect('>') } -> { Instr::Right }
            | { expect(',') } -> { Instr::In }
            | { expect('.') } -> { Instr::Out }
            | { expect('[') } -& bf &- { expect(']') } => { |i| Instr::Loop(i) }
            )*
        }
    }

    let code = "+-+-++!--+]+<.[";

    let error = bf.parse(code.chars().enumerate().collect::<Vec<_>>()).unwrap_err();

    error.print(code);
}
