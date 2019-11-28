#![cfg(feature = "macros")]
#![feature(proc_macro_hygiene)]

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

        print!("  | ");
        for _ in 0..self.found.map(|(idx, _)| idx).unwrap_or(code.len()) {
            print!(" ");
        }
        println!("^");

        let expected_str = self.expected
            .iter()
            .map(|c| format!("'{}'", c))
            .collect::<Vec<_>>()
            .join(", ");
        match self.found {
            Some((idx, c)) => println!("Error at column {}: Unexpected token '{}'.", idx + 1, c),
            None => println!("Error: Unexpected end of file."),
        }

        match self.expected.len() {
            0 => {},
            1 => println!("Note: Expected {}.", expected_str),
            _ => println!("Note: Expected one of {}.", expected_str),
        }
    }
}

impl ParseError<Token> for BrainfuckError {
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
        .link()
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

    // This code contains an error
    let code = "+++!+[->++++<]>[->++++<].";

    let error = bf.parse_str(code).unwrap_err();

    error.print(code);
}
