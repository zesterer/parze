#![feature(trait_alias)]

pub mod error;
pub mod repeat;
mod fail;

use std::{
    rc::Rc,
    cell::RefCell,
    borrow::Borrow,
    ops::{Add, BitOr, Mul, Rem, Sub, Shl, Shr, Not},
};
use crate::{
    error::{ParseError, DefaultParseError},
    repeat::Repeat,
    fail::{Fail, MayFail},
};

type TokenIter<'a, T> = std::iter::Enumerate<std::iter::Cloned<std::slice::Iter<'a, T>>>;

/// A type that represents a rule that may be used to parse a list of symbols.
/// Parsers may be combined and manipulated in various ways to create new parsers.
#[derive(Clone)]
pub struct Parser<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a = DefaultParseError<'a, T>> {
    f: Rc<dyn Fn(&mut TokenIter<T>) -> Result<(MayFail<E>, O), Fail<E>> + 'a>,
}

// Then

impl<'a, T: Clone + 'a, O: 'a, U: 'a, E: ParseError<'a, T> + 'a> Add<Parser<'a, T, U, E>> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, (O, U), E>;
    fn add(self, rhs: Parser<'a, T, U, E>) -> Self::Output { self.then(rhs) }
}

// Or

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> BitOr for Parser<'a, T, O, E> {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output { self.or(rhs) }
}

// Repeat

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a, R: Into<Repeat>> Mul<R> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, Vec<O>, E>;
    fn mul(self, rhs: R) -> Self::Output { self.repeat(rhs.into()) }
}

// Mapping

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a, U: 'a, F: Fn(O) -> U + 'a> Rem<F> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, U, E>;
    fn rem(self, rhs: F) -> Self::Output { self.map(rhs) }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a, U: Clone + 'a> Sub<U> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, U, E>;
    fn sub(self, rhs: U) -> Self::Output { self.to(rhs) }
}

// Padding

impl<'a, T: Clone + 'a, O: 'a, U: 'a, E: ParseError<'a, T> + 'a> Shl<Parser<'a, T, U, E>> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, O, E>;
    fn shl(self, rhs: Parser<'a, T, U, E>) -> Self::Output { self.padded_by(rhs) }
}

impl<'a, T: Clone + 'a, O: 'a, U: 'a, E: ParseError<'a, T> + 'a> Shr<Parser<'a, T, U, E>> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, U, E>;
    fn shr(self, rhs: Parser<'a, T, U, E>) -> Self::Output { self.padding_for(rhs) }
}

// Optional

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Not for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, Option<O>, E>;
    fn not(self) -> Self::Output { self.or_nothing() }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Parser<'a, T, O, E> {
    // Constructor methods

    fn new(f: impl Fn(&mut TokenIter<T>) -> Result<(MayFail<E>, O), Fail<E>> + 'a) -> Self {
        Self { f: Rc::new(move |tokens| attempt(tokens, &f)) }
    }

    fn maybe_map(f: impl Fn(T) -> Option<O> + 'a) -> Self {
        Self::new(move |tokens| try_parse(tokens, |(idx, tok), _| {
            match f(tok.clone()) {
                Some(output) => Ok((MayFail::none(), output)),
                None => Err(Fail::new(idx, E::unexpected(tok))),
            }
        }))
    }

    fn call(f: impl Fn() -> Self + 'a) -> Self {
        Self::new(move |tokens| (f().f)(tokens))
    }

    // Combinator methods

    /// Map the output of this parser to another value with the given function.
    pub fn map<U: 'a>(self, f: impl Fn(O) -> U + 'a) -> Parser<'a, T, U, E> {
        Parser::new(move |tokens| (self.f)(tokens).map(|(e, o)| (e, f(o))))
    }

    /// Discard the output of this parser (i.e: create a parser that outputs `()` instead).
    pub fn discard(self) -> Parser<'a, T, (), E> {
        Parser::new(move |tokens| (self.f)(tokens).map(|(e, _)| (e, ())))
    }

    /// Map all outputs of this parser to the given value.
    pub fn to<U: Clone + 'a>(self, to: U) -> Parser<'a, T, U, E> {
        Parser::new(move |tokens| (self.f)(tokens).map(|(e, _)| (e, to.clone())))
    }

    /// Create a parser that parses symbols that match this parser or not at all.
    pub fn or_nothing(self) -> Parser<'a, T, Option<O>, E> {
        Parser::new(move |tokens| {
            match (self.f)(tokens) {
                Ok((fail, output)) => Ok((fail, Some(output))),
                Err(fail) => Ok((fail.into(), None)),
            }
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    pub fn then<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, (O, U), E> {
        Parser::new(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            let (b_fail, b) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), (a, b)))
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of this parser.
    pub fn padding_for<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, U, E> {
        Parser::new(move |tokens| {
            let (a_fail, _) = (self.f)(tokens)?;
            let (b_fail, b) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), b))
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of the other parser.
    pub fn padded_by<U: 'a>(self, other: Parser<'a, T, U, E>) -> Self {
        Parser::new(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            let (b_fail, _) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), a))
        })
    }

    /// Create a parser that parses symbols that match this parser or another parser.
    pub fn or(self, other: Parser<'a, T, O, E>) -> Self {
        Parser::new(move |tokens| {
            let a = (self.f)(tokens);
            //let mut b_tokens = tokens.clone();
            //let b = (other.f)(&mut b_tokens);
            match a {
                Ok((a_fail, a)) => Ok((a_fail, a)),
                /*
                Ok((a_fail, a)) => match b {
                    Ok((b_fail, _)) => Ok((a_fail.max(b_fail), a)),
                    Err(b_fail) => Ok((a_fail.max(b_fail), a)),
                },
                */
                Err(a_fail) => match (other.f)(tokens) {
                //Err(a_fail) => match b {
                    Ok((b_fail, b)) => {
                        //*tokens = b_tokens;
                        Ok((b_fail.max(a_fail), b))
                    },
                    Err(b_fail) => Err(a_fail.max(b_fail)),
                },
            }
        })
    }

    /// Create a parser that parses symbols that match this parser multiple times, according to the given repetition rule.
    pub fn repeat(self, repeat: impl Into<Repeat>) -> Parser<'a, T, Vec<O>, E> {
        let repeat = repeat.into();
        Parser::new(move |tokens| {
            let mut max_err = MayFail::none();
            let mut outputs = Vec::new();

            for i in 0..repeat.idx_upper_limit() {
                match (self.f)(tokens) {
                    Ok((err, output)) => {
                        max_err = max_err.max(err);
                        outputs.push(output);
                    },
                    Err(err) if repeat.contains(i) => {
                        max_err = max_err.max(err);
                        break;
                    },
                    Err(err) => return Err(err.max(max_err)),
                }
            }

            Ok((max_err, outputs))
        })
    }

    /// Attempt to parse an array-like list of symbols using this parser.
    pub fn parse(&self, tokens: impl AsRef<[T]>) -> Result<O, E> {
        let mut tokens = tokens.as_ref().iter().cloned().enumerate();
        let (fail, output) = (self.f)(&mut tokens).map_err(|e| e.take_error())?;
        if let Some((idx, tok)) = tokens.next() {
            Err(Fail::new(idx, E::unexpected(tok)).max(fail).take_error())
        } else {
            Ok(output)
        }
    }
}

impl<'a, T: Clone + 'a, E: ParseError<'a, T> + 'a> Parser<'a, T, T, E> {
    fn permit(f: impl Fn(T) -> bool + 'a) -> Self {
        Self::maybe_map(move |tok| if f(tok.clone()) { Some(tok) } else { None })
    }

    fn sym(expected: impl Borrow<T> + 'a) -> Self where T: PartialEq {
        Self::permit(move |tok| &tok == expected.borrow())
    }

    fn not_sym(expected: impl Borrow<T> + 'a) -> Self where T: PartialEq {
        Self::permit(move |tok| &tok != expected.borrow())
    }

    fn one_of(expected: impl IntoIterator<Item=impl Borrow<T> + 'static>) -> Self where T: PartialEq {
        let expected = expected.into_iter().collect::<Vec<_>>();
        Self::permit(move |tok| expected.iter().any(|e| &tok == e.borrow()))
    }

    fn not_one_of(expected: impl IntoIterator<Item=impl Borrow<T> + 'static>) -> Self where T: PartialEq {
        let expected = expected.into_iter().collect::<Vec<_>>();
        Self::permit(move |tok| expected.iter().all(|e| &tok != e.borrow()))
    }
}

// Declaration

/// A type used to separate the declaration and definition of a parser such that it may be defined in terms of itself.
/// This type is the primary route through which recursive parsers are defined, although `call(f)` may also be used.
pub struct Declaration<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> = DefaultParseError<'a, T>> {
    parser: Rc<RefCell<Option<Parser<'a, T, O, E>>>>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Declaration<'a, T, O, E> {
    /// Create a new parser declaration.
    pub fn new() -> Self {
        Self { parser: Rc::new(RefCell::new(None)) }
    }

    /// Create a parser that is linked to this declaration.
    /// If the resultant parser is used before this declaration is defined (see `.define(parser)`) then a panic error will occur.
    pub fn link(&self) -> Parser<'a, T, O, E> {
        let parser = self.parser.clone();
        Parser::new(move |tokens| ((*parser).borrow().as_ref().expect("Parser was declared but not defined").f)(tokens))
    }

    /// Provider a parser definition for this declaration, thereby sealing it as a well-defined parser.
    pub fn define(self, parser: Parser<'a, T, O, E>) -> Parser<'a, T, O, E> {
        *self.parser.borrow_mut() = Some(parser);
        self.link()
    }
}

/// Declare a parser before defining it. A definition can be given later with the `.define(parser)` method.
/// This function is generally used to create recursive parsers, along with `call`.
pub fn declare<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>() -> Declaration<'a, T, O, E> {
    Declaration::new()
}

/// A wrapper function for recursive parser declarations.
/// This function uses `Declaration` internally.
pub fn recursive<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl FnOnce(Parser<'a, T, O, E>) -> Parser<'a, T, O, E> + 'a) -> Parser<'a, T, O, E> {
    let p = Declaration::new();
    let p_link = p.link();
    p.define(f(p_link))
}

// Helpers

fn attempt<'a, T: Clone + 'a, R, F, E: ParseError<'a, T> + 'a>(tokens: &mut TokenIter<T>, f: F) -> Result<R, Fail<E>>
    where F: FnOnce(&mut TokenIter<T>) -> Result<R, Fail<E>>,
{
    let mut tokens2 = tokens.clone();
    let tok = f(&mut tokens2)?;
    *tokens = tokens2;
    Ok(tok)
}

fn try_parse<'a, T: Clone + 'a, R, F, E: ParseError<'a, T> + 'a>(tokens: &mut TokenIter<T>, f: F) -> Result<(MayFail<E>, R), Fail<E>>
    where F: FnOnce((usize, T), &mut TokenIter<T>) -> Result<(MayFail<E>, R), Fail<E>>,
{
    attempt(tokens, |tokens| f(tokens.next().ok_or(Fail::new(!0, E::unexpected_end()))?, tokens))
}

// Utility

/// A parser that accepts one a specific symbol.
pub fn sym<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl Borrow<T> + 'static) -> Parser<'a, T, T, E> {
    Parser::sym(expected)
}

/// A parser that accepts any one thing that is not the given symbol.
pub fn not_sym<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl Borrow<T> + 'static) -> Parser<'a, T, T, E> {
    Parser::not_sym(expected)
}

/// A parser that accepts one of the given set of symbols.
pub fn one_of<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl IntoIterator<Item=impl Borrow<T> + 'static>) -> Parser<'a, T, T, E> {
    Parser::one_of(expected)
}

/// A parser that accepts any one symbol that is not within the given set of symbols.
pub fn not_one_of<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl IntoIterator<Item=impl Borrow<T> + 'static>) -> Parser<'a, T, T, E> {
    Parser::not_one_of(expected)
}

/// A parser that accepts one symbol provided it passes the given test.
pub fn permit<'a, T: Clone + 'a, E: ParseError<'a, T> + 'a>(f: impl Fn(T) -> bool + 'static) -> Parser<'a, T, T, E> {
    Parser::permit(f)
}

/// A parser that accepts one symbol provided it passes the given test, mapping it to another symbol in the process.
/// This function is extremely powerful, and in fact it is a supset of `sym`, `not_sym`, `one_of`, `not_one_of` and `permit`.
/// However, this power also makes it fairly awkward to you. You might be better served by one of the aforementioned functions.
pub fn maybe_map<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl Fn(T) -> Option<O> + 'static) -> Parser<'a, T, O, E> {
    Parser::maybe_map(f)
}

/// A parser that invokes another parser, as generated by the given function.
/// This function is generally used to create recursive parsers, along with `Declaration`.
pub fn call<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl Fn() -> Parser<'a, T, O, E> + 'a) -> Parser<'a, T, O, E> {
    Parser::call(f)
}

pub mod prelude {
    pub use super::{
        error::{self, ParseError, DefaultParseError},
        repeat::{self, Repeat, Repeat::Any},
        Parser,
        Declaration,
        declare,
        recursive,
        sym,
        not_sym,
        one_of,
        not_one_of,
        permit,
        maybe_map,
        call,
    };
}

/*
// I wish for this syntax...
parsers! {
    bf =
        | '+' => Token::Add
        | '-' => Token::Sub
        | '<' => Token::Left
        | '>' => Token::Right
        | ',' => Token::In
        | '.' => Token::Out
        | ('[' > bf < ']') => |ts| Token::Loop(ts)
};
*/
