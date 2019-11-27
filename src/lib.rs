//! Parze is a clean, efficient parser combinator written in Rust.
//!
//! # Features
//!
//! - All the usual parser combinator operations
//! - Macro for simple rule and parser declaration
//! - Support for recursive parser definitions
//! - Custom error types - define your own!
//! - Prioritised / merged failure for more useful errors
//! - No dependencies - fast compilation!
//! - `no_std` support
//!
//! # Example
//!
//! A parser capable of parsing all valid Brainfuck code into an AST.
//!
//! ```
//! #![cfg(feature = "macros")]
//! #![feature(proc_macro_hygiene)]
//!
//! use parze::prelude::*;
//!
//! #[derive(Clone, Debug, PartialEq)]
//! enum Instr { Add, Sub, Left, Right, In, Out, Loop(Vec<Instr>) }
//!
//! parsers! {
//!     bf: Parser<_, _> = {
//!         ( '+' -> { Instr::Add }
//!         | '-' -> { Instr::Sub }
//!         | '<' -> { Instr::Left }
//!         | '>' -> { Instr::Right }
//!         | ',' -> { Instr::In }
//!         | '.' -> { Instr::Out }
//!         | '[' -& bf &- ']' => { |ts| Instr::Loop(ts) }
//!         ) *
//!     }
//! }
//! ```

extern crate alloc;

pub mod error;
pub mod repeat;
pub mod also;
pub mod reduce;
pub mod pad;
pub mod chain;
mod fail;

// Reexports

/// A macro to define parser rules.
///
/// # Operators
///
/// Listed in order of precedence
///
/// | Syntax     | Name           | Description                           |
/// |------------|----------------|---------------------------------------|
/// | ~ x        | before padding | Equivalent to `x.before_padding()`    |
/// | x ~        | after padding  | Equivalent to `x.after_padding()`     |
/// | x *        | any            | Equivalent to `x.repeat(..)`          |
/// | x +        | at least one   | Equivalent to `x.repeat(1..)`         |
/// | x ?        | optional       | Equivalent to `x.or_not()`            |
/// | x .%       | chained        | Equivalent to `x.chained()`           |
/// | x .#       | flatten        | Equivalent to `x.flatten()`           |
/// | x ... y    | separated      | Equivalent to `x.separated_by(y)`     |
/// | x & y      | then           | Equivalent to `x.then(y)`             |
/// | x % y      | chain          | Equivalent to `x.chain(y)`            |
/// | x |% y     | or chain       | Equivalent to `x.or_chain(y)`         |
/// | x -& y     | delimiter for  | Equivalent to `x.delimiter_for(y)`    |
/// | x &- y     | delimited by   | Equivalent to `x.delimited_by(y)`     |
/// | x -> Y     | to             | Equivalent to `x.to(y)`               |
/// | x => F     | map            | Equivalent to `x.map(F)`              |
/// | x <: F     | reduce left    | Equivalent to `x.reduce_left(F)`      |
/// | x :> F     | reduce right   | Equivalent to `x.reduce_right(F)`     |
/// | x \| y     | or             | Equivalent to `x.or(y)`               |
/// | { X }      | expr           | Considers `X` to be a Rust expression |
pub use parze_declare::rule;

use alloc::rc::Rc;
use core::{
    slice,
    iter::{self, FromIterator},
    cell::RefCell,
    borrow::Borrow,
    //marker::PhantomData,
    //ops::{Add, BitOr, Mul, Rem, Sub, Shl, Shr, Not},
};
use crate::{
    error::{ParseError, DefaultParseError},
    repeat::Repeat,
    fail::{Fail, MayFail},
    also::Also,
    reduce::{ReduceLeft, ReduceRight},
    pad::Padded,
    chain::{Chain, IntoChain, Single},
};

type TokenIter<'a, T> = iter::Enumerate<iter::Cloned<slice::Iter<'a, T>>>;

type ParseResult<O, E> = Result<(MayFail<E>, O), Fail<E>>;

/// A type that represents a rule that may be used to parse a list of symbols.
///
/// Parsers may be combined and manipulated in various ways to create new parsers.
pub struct Parser<'a, T: Clone + 'a, O: 'a = T, E: ParseError<'a, T> + 'a = DefaultParseError<T>> {
    f: Rc<dyn Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Clone for Parser<'a, T, O, E> {
    fn clone(&self) -> Self {
        Self { f: self.f.clone() }
    }
}

/*
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

// Delimiting

impl<'a, T: Clone + 'a, O: 'a, U: 'a, E: ParseError<'a, T> + 'a> Shl<Parser<'a, T, U, E>> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, O, E>;
    fn shl(self, rhs: Parser<'a, T, U, E>) -> Self::Output { self.delimited_by(rhs) }
}

impl<'a, T: Clone + 'a, O: 'a, U: 'a, E: ParseError<'a, T> + 'a> Shr<Parser<'a, T, U, E>> for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, U, E>;
    fn shr(self, rhs: Parser<'a, T, U, E>) -> Self::Output { self.delimiter_for(rhs) }
}

// Optional

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Not for Parser<'a, T, O, E> {
    type Output = Parser<'a, T, Option<O>, E>;
    fn not(self) -> Self::Output { self.or_not() }
}
*/

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Parser<'a, T, O, E> {
    // Constructor methods

    fn raw(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a) -> Self {
        Self { f: Rc::new(f) }
    }

    fn custom(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a) -> Self {
        Self::raw(move |tokens| attempt(tokens, &f))
    }

    fn try_map(f: impl Fn(T) -> Result<O, E> + 'a) -> Self {
        Self::raw(move |tokens| try_parse(tokens, |(idx, tok), _| {
            match f(tok.clone()) {
                Ok(output) => Ok((MayFail::none(), output)),
                Err(err) => Err(Fail::new(idx, err)),
            }
        }))
    }

    fn call(f: impl Fn() -> Self + 'a) -> Self {
        Self::custom(move |tokens| (f().f)(tokens))
    }

    // Undocumented
    pub fn link(&self) -> Self {
        self.clone()
    }

    // Combinator methods

    /// Map the output of this parser to another value with the given function.
    pub fn map<U: 'a>(self, f: impl Fn(O) -> U + 'a) -> Parser<'a, T, U, E> {
        Parser::custom(move |tokens| (self.f)(tokens).map(|(e, o)| (e, f(o))))
    }

    /// Map the error of this parser to another with the given function.
    ///
    /// This may be used to annotate an error with contextual information at some stage of parsing.
    pub fn map_err<G: ParseError<'a, T> + 'a>(self, f: impl Fn(E) -> G + 'a) -> Parser<'a, T, O, G> {
        Parser::custom(move |tokens| match (self.f)(tokens) {
            Ok((fail, output)) => Ok((fail.map_err(&f), output)),
            Err(fail) => Err(fail.map_err(&f)),
        })
    }

    /// Discard the output of this parser (i.e: create a parser that outputs `()` instead).
    pub fn discard(self) -> Parser<'a, T, (), E> {
        self.map(|_| ())
    }

    /// Map all outputs of this parser to the given value.
    pub fn to<U: Clone + 'a>(self, to: U) -> Parser<'a, T, U, E> {
        self.map(move |_| to.clone())
    }

    /// Create a parser that optionally parses symbols that match this parser.
    pub fn or_not(self) -> Parser<'a, T, Option<O>, E> {
        Parser::custom(move |tokens| {
            match (self.f)(tokens) {
                Ok((fail, output)) => Ok((fail, Some(output))),
                Err(fail) => Ok((fail.into(), None)),
            }
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    pub fn then<U: 'a>(self, other: impl Into<Parser<'a, T, U, E>>) -> Parser<'a, T, (O, U), E> {
        let other = other.into();
        Parser::custom(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            match (other.f)(tokens) {
                Ok((b_fail, b)) => Ok((a_fail.max(b_fail), (a, b))),
                Err(b_fail) => Err(b_fail.max(a_fail)),
            }
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    ///
    /// Whereas `.then` turns outputs of `(T, U)` and `V` into `((T, U), V)`, this method turns them into `(T, U, V)`.
    /// Due to current limitations in Rust's type system, this method is significantly less useful than it could be.
    pub fn also<U: 'a>(self, other: impl Into<Parser<'a, T, U, E>>) -> Parser<'a, T, O::Alsoed, E> where O: Also<U> {
        let other = other.into();
        Parser::custom(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            match (other.f)(tokens) {
                Ok((b_fail, b)) => Ok((a_fail.max(b_fail), a.also(b))),
                Err(b_fail) => Err(b_fail.max(a_fail)),
            }
        })
    }

    /*
    /// Create a parser that parses symbols that match this parser and then another parser.
    ///
    /// Unlike `.then`, this method will chain the two parser outputs together as a vector.
    pub fn chain<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, O::Chained, E> where O: Chain<U> {
        self.then(other).map(|(a, b)| a.chain(b))
    }
    */

    /// Create a parser that parsers the same symbols as this parser, but emits its output as a vector
    ///
    /// This is most useful when you wish to use singular outputs as part of a chain.
    pub fn chained(self) -> Parser<'a, T, impl Chain<Item=O>, E> {
        self.map(|output| Single::from(output))
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    ///
    /// Unlike `.then`, this method will chain the two parser outputs together as a vector.
    pub fn chain<U: 'a, V: 'a>(self, other: impl Into<Parser<'a, T, U, E>>) -> Parser<'a, T, impl Chain<Item=V>, E>
        where O: IntoChain<Item=V>, U: IntoChain<Item=V>
    {
        self.then(other.into()).map(|(a, b)| a.into_chain().into_iter_chain().chain(b.into_chain().into_iter_chain()).collect::<Vec<_>>())
    }

    /// Create a parser that with a flatter output than this parser.
    pub fn flatten<U: 'a, V: 'a>(self) -> Parser<'a, T, impl Chain<Item=V>, E>
        where O: IntoChain<Item=U>, U: IntoChain<Item=V>
    {
        self.map(|a| a.into_chain().into_iter_chain().map(|a| a.into_chain().into_iter_chain()).flatten().collect::<Vec<_>>())
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of this parser.
    pub fn delimiter_for<U: 'a>(self, other: impl Into<Parser<'a, T, U, E>>) -> Parser<'a, T, U, E> {
        let other = other.into();
        Parser::custom(move |tokens| {
            let (a_fail, _) = (self.f)(tokens)?;
            match (other.f)(tokens) {
                Ok((b_fail, b)) => Ok((a_fail.max(b_fail), b)),
                Err(b_fail) => Err(b_fail.max(a_fail)),
            }
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of the other parser.
    pub fn delimited_by<U: 'a>(self, other: impl Into<Parser<'a, T, U, E>>) -> Self {
        let other = other.into();
        Parser::custom(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            match (other.f)(tokens) {
                Ok((b_fail, _)) => Ok((a_fail.max(b_fail), a)),
                Err(b_fail) => Err(b_fail.max(a_fail)),
            }
        })
    }

    /// Create a parser that accepts the valid input of this parser separated by the valid input of another.
    pub fn separated_by<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, Vec<O>, E> {
        Parser::custom(move |tokens| {
            let mut max_err = MayFail::none();
            let mut outputs = Vec::new();

            for i in 0.. {
                match (self.f)(tokens) {
                    Ok((err, output)) => {
                        max_err = max_err.max(err);
                        outputs.push(output);
                    },
                    Err(err) if i == 0 => {
                        max_err = max_err.max(err);
                        break;
                    },
                    Err(err) => return Err(err.max(max_err)),
                }

                match (other.f)(tokens) {
                    Ok((err, _)) => max_err = max_err.max(err),
                    Err(err) => {
                        max_err = max_err.max(err);
                        break;
                    },
                }
            }

            Ok((max_err, outputs))
        })

        //self.clone().delimited_by(other).repeat(..).chain(self.repeat(1)).or_not().flatten()
    }

    /// Create a parser that parses character-like symbols that match this parser followed or preceded by any number of 'padding' (usually taken to mean whitespace) symbols.
    ///
    /// You can implement the `Padded` trait for your own symbol types to use this method with them.
    pub fn padded<U: Padded>(self) -> Self where T: Borrow<U> {
        self.before_padding().after_padding()
    }

    /// Create a parser that parses any symbols that match this parser followed by any number of 'padding' (usually taken to mean whitespace) symbols.
    ///
    /// You can implement the `Padded` trait for your own symbol types to use this method with them.
    pub fn before_padding<U: Padded>(self) -> Self where T: Borrow<U> {
        self.delimited_by(padding())
    }

    /// Create a parser that parses any number of 'padding' (usually taken to mean whitespace) symbols followed by any symbols that match this parser.
    ///
    /// You can implement the `Padded` trait for your own symbol types to use this method with them.
    pub fn after_padding<U: Padded>(self) -> Self where T: Borrow<U> {
        padding().delimiter_for(self)
    }

    /// Create a parser that parses symbols that match this parser or another parser.
    pub fn or(self, other: impl Into<Parser<'a, T, O, E>>) -> Self {
        let other = other.into();
        Parser::custom(move |tokens| {
            let a = (self.f)(tokens);
            let mut b_tokens = tokens.clone();
            let b = (other.f)(&mut b_tokens);
            match a {
                Ok((a_fail, a)) => match b {
                    Ok((b_fail, _)) => Ok((a_fail.max(b_fail), a)),
                    Err(b_fail) => Ok((a_fail.max(b_fail), a)),
                },
                Err(a_fail) => match b {
                    Ok((b_fail, b)) => {
                        *tokens = b_tokens;
                        Ok((b_fail.max(a_fail), b))
                    },
                    Err(b_fail) => Err(a_fail.max(b_fail)),
                },
            }
        })
    }

    /// Create a parser that parses symbols that match this parser or another parser where both parsers are chains.
    pub fn or_chain<U, V: 'a>(self, other: impl Into<Parser<'a, T, V, E>>) -> Parser<'a, T, impl Chain<Item=U>, E>
        where V: IntoChain<Item=U>, O: IntoChain<Item=U>
    {
        let other = other.into();
        Parser::custom(move |tokens| {
            let a = (self.f)(tokens);
            let mut b_tokens = tokens.clone();
            let b = (other.f)(&mut b_tokens);
            match a {
                Ok((a_fail, a)) => match b {
                    Ok((b_fail, _)) => Ok((a_fail.max(b_fail), a.into_chain().into_iter_chain().collect::<Vec<_>>())),
                    Err(b_fail) => Ok((a_fail.max(b_fail), a.into_chain().into_iter_chain().collect())),
                },
                Err(a_fail) => match b {
                    Ok((b_fail, b)) => {
                        *tokens = b_tokens;
                        Ok((b_fail.max(a_fail), b.into_chain().into_iter_chain().collect()))
                    },
                    Err(b_fail) => Err(a_fail.max(b_fail)),
                },
            }
        })
    }

    /// Create a parser that parses symbols that match this parser or another fallback parser, prioritising errors from this parser.
    ///
    /// This method is 'short-circuiting': if this parser succeeds, the fallback parser won't even be invoked.
    /// This means that emitted errors may not include information from the fallback parser.
    pub fn or_fallback(self, other: impl Into<Parser<'a, T, O, E>>) -> Self {
        let other = other.into();
        Parser::custom(move |tokens| {
            let a = (self.f)(tokens);
            match a {
                Ok((a_fail, a)) => Ok((a_fail, a)),
                Err(a_fail) => match (other.f)(tokens) {
                    Ok((b_fail, b)) => Ok((b_fail.max(a_fail), b)),
                    Err(b_fail) => Err(a_fail.max(b_fail)),
                },
            }
        })
    }

    /// Create a parser that parses symbols that match this parser multiple times, according to the given repetition rule.
    pub fn repeat(self, repeat: impl Into<Repeat>) -> Parser<'a, T, Vec<O>, E> {
        let repeat = repeat.into();
        Parser::custom(move |tokens| {
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

    /// Create a parser that parses symbols that match this parser and then another parser.
    pub fn collect<U: FromIterator<O::Item>>(self) -> Parser<'a, T, U, E> where O: IntoIterator {
        self.map(|output| output.into_iter().collect())
    }

    /// Create a parser that left-reduces this parser down into another type according to the given reduction function.
    pub fn reduce_left<A, B>(self, f: impl Fn(B, A) -> A + 'a) -> Parser<'a, T, A, E> where O: ReduceLeft<A, B> {
        self.map(move |output| output.reduce_left(&f))
    }

    /// Create a parser that right-reduces this parser down into another type according to the given reduction function.
    pub fn reduce_right<A, B>(self, f: impl Fn(A, B) -> A + 'a) -> Parser<'a, T, A, E> where O: ReduceRight<A, B> {
        self.map(move |output| output.reduce_right(&f))
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

impl<'a, T: Clone + 'a, E: ParseError<'a, T> + 'a> Parser<'a, T, (), E> {
    fn padding<U: Padded>() -> Self where T: Borrow<U> {
        Self::custom(|tokens| {
            while tokens
                .clone()
                .next()
                .map(|(_, token)| token.borrow().is_padding())
                .unwrap_or(false)
            {
                tokens.next();
            }

            Ok((MayFail::none(), ()))
        })
    }
}

impl<'a, T: Clone + 'a, E: ParseError<'a, T> + 'a> Parser<'a, T, T, E> {
    fn permit(f: impl Fn(T) -> bool + 'a) -> Self {
        Self::try_map(move |tok| if f(tok.clone()) { Ok(tok) } else { Err(E::unexpected(tok)) })
    }

    fn sym(expected: impl Borrow<T> + 'a) -> Self where T: PartialEq {
        Self::permit(move |tok| &tok == expected.borrow())
    }

    fn not_sym(expected: impl Borrow<T> + 'a) -> Self where T: PartialEq {
        Self::permit(move |tok| &tok != expected.borrow())
    }

    fn one_of(expected: impl IntoIterator<Item=impl Borrow<T> + 'a>) -> Self where T: PartialEq {
        let expected = expected.into_iter().collect::<Vec<_>>();
        Self::permit(move |tok| expected.iter().any(|e| &tok == e.borrow()))
    }

    fn none_of(expected: impl IntoIterator<Item=impl Borrow<T> + 'a>) -> Self where T: PartialEq {
        let expected = expected.into_iter().collect::<Vec<_>>();
        Self::permit(move |tok| expected.iter().all(|e| &tok != e.borrow()))
    }

    fn all_of(expected: impl IntoIterator<Item=impl Borrow<T> + 'a>) -> Parser<'a, T, Vec<T>, E> where T: PartialEq {
        let expected = expected.into_iter().collect::<Vec<_>>();
        Parser::custom(move |tokens| {
            let mut outputs = Vec::new();
            for expected in &expected {
                match tokens.next() {
                    Some((_, output)) if &output == expected.borrow() => outputs.push(output),
                    Some((idx, output)) => return Err(Fail::new(idx, E::unexpected(output))),
                    None => return Err(Fail::new(!0, E::unexpected_end())),
                }
            }
            Ok((MayFail::none(), outputs))
        })
    }
}

// Declaration

/// A type used to separate the declaration and definition of a parser such that it may be defined in terms of itself.
///
/// This type is the primary route through which recursive parsers are defined, although `call(f)` may also be used.
pub struct Declaration<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> = DefaultParseError<T>> {
    parser: Rc<RefCell<Option<Parser<'a, T, O, E>>>>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>> Default for Declaration<'a, T, O, E> {
    fn default() -> Self {
        Self { parser: Rc::new(RefCell::new(None)) }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Declaration<'a, T, O, E> {
    /// Create a parser that is linked to this declaration.
    /// If the resultant parser is used before this declaration is defined (see `.define`) then a panic will occur.
    pub fn link(&self) -> Parser<'a, T, O, E> {
        let parser = Rc::downgrade(&self.parser);
        Parser::custom(move |tokens| {
            ((*parser.upgrade().expect("Parser was dropped")).borrow().as_ref().expect("Parser was declared but not defined").f)(tokens)
        })
    }

    /// Provider a parser definition for this declaration, thereby sealing it as a well-defined parser.
    pub fn define(self, parser: Parser<'a, T, O, E>) -> Parser<'a, T, O, E> {
        *self.parser.borrow_mut() = Some(parser);
        Parser::custom(move |tokens| ((*self.parser).borrow().as_ref().unwrap().f)(tokens))
    }
}

/// Declare a parser before defining it. A definition can be given later with the `.define` method.
///
/// This function is generally used to create recursive parsers, along with `call`.
pub fn declare<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>() -> Declaration<'a, T, O, E> {
    Declaration::default()
}

/// A wrapper function for recursive parser declarations.
///
/// This function uses `Declaration` internally.
pub fn recursive<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl FnOnce(Parser<'a, T, O, E>) -> Parser<'a, T, O, E> + 'a) -> Parser<'a, T, O, E> {
    let p = Declaration::default();
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
    attempt(tokens, |tokens| f(tokens.next().ok_or_else(|| Fail::new(!0, E::unexpected_end()))?, tokens))
}

// Utility

/// A parser that accepts the given symbol.
pub fn sym<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl Borrow<T> + 'a) -> Parser<'a, T, T, E> {
    Parser::sym(expected)
}

/// A parser that accepts any one thing that is not the given symbol.
pub fn not_sym<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl Borrow<T> + 'a) -> Parser<'a, T, T, E> {
    Parser::not_sym(expected)
}

/// A parser that accepts one of the given set of symbols.
pub fn one_of<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl IntoIterator<Item=impl Borrow<T> + 'a>) -> Parser<'a, T, T, E> {
    Parser::one_of(expected)
}

/// A parser that accepts any one symbol that is not within the given set of symbols.
pub fn none_of<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl IntoIterator<Item=impl Borrow<T> + 'a>) -> Parser<'a, T, T, E> {
    Parser::none_of(expected)
}

/// A parser that accepts all of the given list of symbols, one after another.
pub fn all_of<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>(expected: impl IntoIterator<Item=impl Borrow<T> + 'static>) -> Parser<'a, T, Vec<T>, E> {
    Parser::all_of(expected)
}

/// A parser that accepts one symbol provided it passes the given test.
pub fn permit<'a, T: Clone + 'a, E: ParseError<'a, T> + 'a>(f: impl Fn(T) -> bool + 'static) -> Parser<'a, T, T, E> {
    Parser::permit(f)
}

/// A parser that accepts one symbol provided it passes the given test, mapping it to another symbol in the process.
///
/// This function is extremely powerful, and is actually a superset of several other parser functions defined in this crate.
/// However, this power also makes it fairly awkward to use. You might be better served by another function.
pub fn try_map<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl Fn(T) -> Result<O, E> + 'static) -> Parser<'a, T, O, E> {
    Parser::try_map(f)
}

/// A parser that accepts one symbol provided it passes the given test, mapping it to another symbol in the process.
pub fn maybe_map<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl Fn(T) -> Option<O> + 'static) -> Parser<'a, T, O, E> {
    Parser::try_map(move |tok: T| f(tok.clone()).ok_or(E::unexpected(tok)))
}

/// A parser that accepts any single symbol.
pub fn any_sym<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>() -> Parser<'a, T, T, E> {
    permit(|_| true)
}

/// A parser that accepts all input symbols.
pub fn all_sym<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>() -> Parser<'a, T, Vec<T>, E> {
    permit(|_| true).repeat(..)
}

/// A parser that accepts no input symbols.
pub fn nothing<'a, T: Clone + 'a + PartialEq, E: ParseError<'a, T> + 'a>() -> Parser<'a, T, (), E> {
    permit(|_| false).discard()
}

/// A parser that accepts any number of 'padding' symbols. Usually, this is taken to mean whitespace.
///
/// You can implement the `Padded` trait for your own symbol types to use this function with them.
pub fn padding<'a, T: Clone + 'a, U: Padded, E: ParseError<'a, T> + 'a>() -> Parser<'a, T, (), E> where T: Borrow<U> {
    Parser::padding()
}

/// A parser that invokes another parser, as generated by the given function.
///
/// This function is generally used to create recursive parsers, along with `Declaration`.
pub fn call<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl Fn() -> Parser<'a, T, O, E> + 'a) -> Parser<'a, T, O, E> {
    Parser::call(f)
}

pub mod prelude {
    pub use super::{
        error::{self, ParseError, DefaultParseError},
        repeat::{self, Repeat, Repeat::Any},
        chain::{Chain, IntoChain},
        Parser,
        Declaration,
        declare,
        recursive,
        sym,
        not_sym,
        one_of,
        none_of,
        all_of,
        permit,
        padding,
        maybe_map,
        call,
        rule,
        parsers,
    };
}

#[cfg(feature = "macros")]
#[macro_export]
macro_rules! parze_error {
    () => {};
}

/// A macro to define recursive parsers.
///
/// Parsers defined by this macro may be arbitrarily self-referential, unlike `rule!`.
///
/// # Example
///
/// ```
/// #![cfg(feature = "macros")]
/// #![feature(proc_macro_hygiene)]
///
/// use parze::prelude::*;
///
/// parsers! {
///     foo = {
///         '!' | bar
///     }

///     bar: Parser<_, _> = {
///         '(' -& foo &- ')'
///     }
/// }
/// ```
#[cfg(feature = "macros")]
#[macro_export]
macro_rules! parsers {
    ( @NAMES ) => {};
    ( @NAMES $name:ident : $kind:ty = { $($rule:tt)* } $($tail:tt)* ) => {
        let $name = $crate::declare();
        $crate::parsers!(@NAMES $($tail)*);
    };
    ( @NAMES $name:ident = { $($rule:tt)* } $($tail:tt)* ) => {
        $crate::parsers!(@NAMES $name : _ = { $($rule)* } $($tail)*);
    };
    ( @NAMES $($tail:tt)* ) => {
        $crate::parze_error!($($tail)*);
    };

    ( @DEFINITIONS ) => {};
    ( @DEFINITIONS $name:ident : $kind:ty = { $($rule:tt)* } $($tail:tt)* ) => {
        let __tmp = $crate::rule!($($rule)*);
        let $name : $kind = ($name).define(__tmp);
        $crate::parsers!(@DEFINITIONS $($tail)*);
    };
    ( @DEFINITIONS $name:ident = { $($rule:tt)* } $($tail:tt)* ) => {
        $crate::parsers!(@DEFINITIONS $name : _ = { $($rule)* } $($tail)*);
    };
    ( @DEFINITIONS $($tail:tt)* ) => {
        $crate::parze_error!($($tail)*);
    };

    ( $($tail:tt)* ) => {
        $crate::parsers!(@NAMES $($tail)*);
        $crate::parsers!(@DEFINITIONS $($tail)*);
    };
}


