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
//!     bf: Parser<char, _> = {
//!         ( '+' -> { Instr::Add }
//!         | '-' -> { Instr::Sub }
//!         | '<' -> { Instr::Left }
//!         | '>' -> { Instr::Right }
//!         | ',' -> { Instr::In }
//!         | '.' -> { Instr::Out }
//!         | '[' -& bf &- ']' => { |i| Instr::Loop(i) }
//!         ) *
//!     }
//! }
//! ```

extern crate alloc;

pub mod error;
pub mod repeat;
pub mod reduce;
pub mod pad;
pub mod chain;
pub mod parse_fn;
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
/// | x .@       | link           | Equivalent to `x.link()`              |
/// | x ... y    | separated      | Equivalent to `x.separated_by(y)`     |
/// | x & y      | then           | Equivalent to `x.then(y)`             |
/// | x % y      | chain          | Equivalent to `x.chain(y)`            |
/// | x \|% y    | or chain       | Equivalent to `x.or_chain(y)`         |
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
    marker::PhantomData,
};
use crate::{
    error::{ParseError, DefaultParseError},
    repeat::Repeat,
    fail::{Fail, MayFail},
    reduce::{ReduceLeft, ReduceRight},
    pad::Padded,
    chain::{Chain, IntoChain, Single},
    parse_fn::{
        ParseFn, RcParseFn, GenParseFn,
        ThenFn, ChainFn,
        OrFn, OrFallbackFn, OrChainFn, OrChainFallbackFn,
    },
};

type TokenIter<'a, T> = iter::Enumerate<iter::Cloned<slice::Iter<'a, T>>>;

type ParseResult<O, E> = Result<(MayFail<E>, O), Fail<E>>;

/// A type that represents a rule that may be used to parse a list of symbols.
///
/// Parsers may be combined and manipulated in various ways to create new parsers.
pub struct Parser<'a, T, O = T, E = DefaultParseError<T>, F = RcParseFn<'a, T, O, E>>
    where
        T: Clone + 'a,
        O: 'a,
        E: ParseError<T> + 'a,
        F: ParseFn<T, O, E> + 'a,
{
    f: F,
    _phantom: PhantomData<&'a (T, O, E)>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a, F: ParseFn<T, O, E> + 'a> Clone for Parser<'a, T, O, E, F> {
    fn clone(&self) -> Self {
        Self {
            f: self.f.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a> Parser<'a, T, O, E> {
    fn dynamic_raw(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a) -> Self {
        Parser {
            f: RcParseFn::new(f),
            _phantom: PhantomData,
        }
    }

    fn dynamic(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a) -> Self {
        Self::dynamic_raw(move |tokens| attempt(tokens, &f))
    }

    fn generic_raw<'b>(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone + 'a) -> Parser<'b, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser {
            f: GenParseFn::new(f),
            _phantom: PhantomData,
        }
    }

    fn generic<'b>(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone + 'a) -> Parser<'b, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        // TODO: Switch to `Self::generic_raw`
        Self::dynamic_raw(move |tokens| attempt(tokens, &f))
    }

    fn try_map<'b>(f: impl Fn(T) -> Result<O, E> + Clone + 'a) -> Parser<'b, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Self::generic_raw(move |tokens| try_parse(tokens, |(idx, tok), _| {
            match f(tok.clone()) {
                Ok(output) => Ok((MayFail::none(), output)),
                Err(err) => Err(Fail::new(idx, err)),
            }
        }))
    }
}

pub trait Captures<'a> {}
impl<'a, T: ?Sized> Captures<'a> for T {}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a, F: ParseFn<T, O, E> + 'a> Parser<'a, T, O, E, F> {
    fn new(f: F) -> Self {
        Self {
            f,
            _phantom: PhantomData,
        }
    }

    fn call(f: impl Fn() -> Self + 'a) -> Parser<'a, T, O, E> {
        Parser::dynamic(move |tokens| f().f.parse(tokens))
    }

    /// Convert this parser into one with a standard payload that may be accepted by more functions
    pub fn to_object(&self) -> Parser<'a, T, O, E> {
        let this = self.clone();
        Parser::dynamic_raw(move |tokens| this.f.parse(tokens))
    }

    /// Undocumented
    pub fn link(&self) -> Self {
        self.clone()
    }

    // Combinator methods

    /// Map the output of this parser to another value with the given function.
    pub fn map<'b, U: 'a>(self, f: impl Fn(O) -> U + Clone + 'a) -> Parser<'a, T, U, E, impl ParseFn<T, U, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::generic_raw(move |tokens| self.f.parse(tokens).map(|(e, o)| (e, f(o))))
    }

    /// Map the error of this parser to another with the given function.
    ///
    /// This may be used to annotate an error with contextual information at some stage of parsing.
    pub fn map_err<'b, G: ParseError<T> + 'a>(self, f: impl Fn(E) -> G + Clone + 'a) -> Parser<'a, T, O, G, impl ParseFn<T, O, G> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::generic_raw(move |tokens| match self.f.parse(tokens) {
            Ok((fail, output)) => Ok((fail.map_err(&f), output)),
            Err(fail) => Err(fail.map_err(&f)),
        })
    }

    /// Discard the output of this parser (i.e: create a parser that outputs `()` instead).
    pub fn discard<'b>(self) -> Parser<'a, T, (), E, impl ParseFn<T, (), E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        self.map(|_| ())
    }

    /// Map all outputs of this parser to the given value.
    pub fn to<'b, U: Clone + 'a>(self, to: U) -> Parser<'a, T, U, E, impl ParseFn<T, U, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        self.map(move |_| to.clone())
    }

    /// Create a parser that optionally parses symbols that match this parser.
    pub fn or_not<'b>(self) -> Parser<'a, T, Option<O>, E, impl ParseFn<T, Option<O>, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::generic_raw(move |tokens| {
            match self.f.parse(tokens) {
                Ok((fail, output)) => Ok((fail, Some(output))),
                Err(fail) => Ok((fail.into(), None)),
            }
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    pub fn then<'b, U: 'b, G: ParseFn<T, U, E> + 'b>(self, other: Parser<'a, T, U, E, G>) -> Parser<'a, T, (O, U), E, impl ParseFn<T, (O, U), E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::new(ThenFn(self.f, other.f))
    }

    /// Create a parser that parsers the same symbols as this parser, but emits its output as a chain.
    ///
    /// This is most useful when you wish to use singular outputs as part of a chain.
    pub fn chained<'b>(self) -> Parser<'a, T, Single<O>, E, impl ParseFn<T, Single<O>, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        self.map(|output| Single::from(output))
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    ///
    /// Unlike `.then`, this method will chain the two parser outputs together as a chain.
    pub fn chain<'b, U: 'a, V: 'a, G: ParseFn<T, U, E> + 'a>(self, other: Parser<'a, T, U, E, G>) -> Parser<'a, T, Vec<V>, E, impl ParseFn<T, Vec<V>, E> + Captures<'b> + 'a>
        where O: IntoChain<Item=V>, U: IntoChain<Item=V>, 'a: 'b, 'b: 'a
    {
        Parser::new(ChainFn(self.f, other.f, PhantomData))
    }

    /// Create a parser that with a flatter output than this parser.
    pub fn flatten<'b, U: 'a, V: 'a>(self) -> Parser<'a, T, Vec<V>, E, impl ParseFn<T, Vec<V>, E> + Captures<'b> + 'a>
        where O: IntoChain<Item=U>, U: IntoChain<Item=V>, 'a: 'b, 'b: 'a
    {
        self.map(|a| a.into_chain().into_iter_chain().map(|a| a.into_chain().into_iter_chain()).flatten().collect::<Vec<_>>())
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of this parser.
    pub fn delimiter_for<'b, U: 'a>(self, other: Parser<'a, T, U, E, impl ParseFn<T, U, E>>) -> Parser<'a, T, U, E, impl ParseFn<T, U, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        self.then(other).map(|(_, b)| b)
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of the other parser.
    pub fn delimited_by<'b, U: 'a>(self, other: Parser<'a, T, U, E, impl ParseFn<T, U, E>>) -> Parser<'a, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        self.then(other).map(|(a, _)| a)
    }

    /// Create a parser that accepts the valid input of this parser separated by the valid input of another.
    pub fn separated_by<'b, U: 'a>(self, other: Parser<'a, T, U, E, impl ParseFn<T, U, E>>) -> Parser<'a, T, Vec<O>, E, impl ParseFn<T, Vec<O>, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::generic(move |tokens| {
            let mut max_err = MayFail::none();
            let mut outputs = Vec::new();

            let mut old_tokens = tokens.clone();

            for i in 0.. {
                match self.f.parse(tokens) {
                    Ok((err, output)) => {
                        max_err = max_err.max(err);
                        outputs.push(output);
                    },
                    Err(err) => {
                        max_err = max_err.max(err);
                        *tokens = old_tokens;
                        break;
                    },
                }

                old_tokens = tokens.clone();

                match other.f.parse(tokens) {
                    Ok((err, _)) => max_err = max_err.max(err),
                    Err(err) => {
                        max_err = max_err.max(err);
                        break;
                    },
                }
            }

            Ok((max_err, outputs))
        })
    }

    /// Create a parser that parses character-like symbols that match this parser followed or preceded by any number of 'padding' (usually taken to mean whitespace) symbols.
    ///
    /// You can implement the `Padded` trait for your own symbol types to use this method with them.
    pub fn padded<'b, U: Padded>(self) -> Parser<'a, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where T: Borrow<U>, 'a: 'b, 'b: 'a
    {
        self.after_padding().before_padding()
    }

    /// Create a parser that parses any symbols that match this parser followed by any number of 'padding' (usually taken to mean whitespace) symbols.
    ///
    /// You can implement the `Padded` trait for your own symbol types to use this method with them.
    pub fn before_padding<'b, U: Padded>(self) -> Parser<'a, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where T: Borrow<U>, 'a: 'b, 'b: 'a
    {
        self.delimited_by(padding())
    }

    /// Create a parser that parses any number of 'padding' (usually taken to mean whitespace) symbols followed by any symbols that match this parser.
    ///
    /// You can implement the `Padded` trait for your own symbol types to use this method with them.
    pub fn after_padding<'b, U: Padded>(self) -> Parser<'a, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where T: Borrow<U>, 'a: 'b, 'b: 'a
    {
        padding().delimiter_for(self)
    }

    /// Create a parser that parses symbols that match this parser or another parser.
    pub fn or<'b>(self, other: Parser<'b, T, O, E, impl ParseFn<T, O, E>>) -> Parser<'b, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::new(OrFn(self.f, other.f))
    }

    /// Create a parser that parses symbols that match this parser or another parser where both parsers are chains.
    pub fn or_chain<V: 'a, U: 'a, G: ParseFn<T, U, E>>(self, other: Parser<'a, T, U, E, G>) -> Parser<'a, T, Vec<V>, E, OrChainFn<F, G, O, U>>
        where O: IntoChain<Item=V>, U: IntoChain<Item=V>
    {
        Parser::new(OrChainFn(self.f, other.f, PhantomData))
    }

    /// Create a parser that parses symbols that match this parser or another fallback parser where both parsers are chains, prioritising errors from this parser.
    ///
    /// This method is 'short-circuiting': if this parser succeeds, the fallback parser won't even be invoked.
    /// This means that emitted errors may not include information from the fallback parser.
    pub fn or_chain_fallback<V: 'a, U: 'a, G: ParseFn<T, U, E>>(self, other: Parser<'a, T, U, E, G>) -> Parser<'a, T, Vec<V>, E, OrChainFallbackFn<F, G, O, U>>
        where O: IntoChain<Item=V>, U: IntoChain<Item=V>
    {
        Parser::new(OrChainFallbackFn(self.f, other.f, PhantomData))
    }

    /// Create a parser that parses symbols that match this parser or another fallback parser, prioritising errors from this parser.
    ///
    /// This method is 'short-circuiting': if this parser succeeds, the fallback parser won't even be invoked.
    /// This means that emitted errors may not include information from the fallback parser.
    pub fn or_fallback<'b, G: ParseFn<T, O, E>>(self, other: Parser<'a, T, O, E, G>) -> Parser<'b, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        Parser::new(OrFallbackFn(self.f, other.f))
    }

    /// Create a parser that parses symbols that match this parser multiple times, according to the given repetition rule.
    pub fn repeat<'b>(self, repeat: impl Into<Repeat>) -> Parser<'a, T, Vec<O>, E, impl ParseFn<T, Vec<O>, E> + Captures<'b> + 'a>
        where 'a: 'b, 'b: 'a
    {
        let repeat = repeat.into();
        Parser::generic(move |tokens| {
            let mut max_err = MayFail::none();
            let mut outputs = Vec::new();

            for i in 0..repeat.idx_upper_limit() {
                match self.f.parse(tokens) {
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
    pub fn collect<'b, U: FromIterator<O::Item>>(self) -> Parser<'a, T, U, E, impl ParseFn<T, U, E> + Captures<'b> + 'a>
        where O: IntoIterator, 'a: 'b, 'b: 'a
    {
        self.map(|output| output.into_iter().collect())
    }

    /// Create a parser that left-reduces this parser down into another type according to the given reduction function.
    pub fn reduce_left<'b, A, B>(self, f: impl Fn(B, A) -> A + Clone + 'a) -> Parser<'a, T, A, E, impl ParseFn<T, A, E> + Captures<'b> + 'a>
        where O: ReduceLeft<A, B>, 'a: 'b, 'b: 'a
    {
        self.map(move |output| output.reduce_left(&f))
    }

    /// Create a parser that right-reduces this parser down into another type according to the given reduction function.
    pub fn reduce_right<'b, A, B>(self, f: impl Fn(A, B) -> A + Clone + 'a) -> Parser<'a, T, A, E, impl ParseFn<T, A, E> + Captures<'b> + 'a>
        where O: ReduceRight<A, B>, 'a: 'b, 'b: 'a
    {
        self.map(move |output| output.reduce_right(&f))
    }

    /// Attempt to parse an array-like list of symbols using this parser.
    pub fn parse(&self, tokens: &[T]) -> Result<O, E> {
        let mut tokens = tokens.iter().cloned().enumerate();
        let (fail, output) = self.f.parse(&mut tokens).map_err(|e| e.take_error())?;
        if let Some((idx, tok)) = tokens.next() {
            Err(Fail::new(idx, E::unexpected(tok)).max(fail).take_error())
        } else {
            Ok(output)
        }
    }
}

impl<'a, O: 'a, E: ParseError<char> + 'a, F: ParseFn<char, O, E> + 'a> Parser<'a, char, O, E, F> {
    /// Attempt to parse a string using this parser.
    pub fn parse_str(&self, string: impl AsRef<str>) -> Result<O, E> {
        // I'd like to find a way around doing this... alas, I can't think of one other than boxing the iterator.
        self.parse(&string.as_ref().chars().collect::<Vec<_>>())
    }
}

// Declaration

/// A type used to separate the declaration and definition of a parser such that it may be defined in terms of itself.
///
/// This type is the primary route through which recursive parsers are defined, although `call(f)` may also be used.
pub struct Declaration<'a, T: Clone + 'a, O: 'a, E: ParseError<T> = DefaultParseError<T>> {
    parser: Rc<RefCell<Option<Parser<'a, T, O, E>>>>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<T>> Default for Declaration<'a, T, O, E> {
    fn default() -> Self {
        Self { parser: Rc::new(RefCell::new(None)) }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a> Declaration<'a, T, O, E> {
    /// Create a parser that is linked to this declaration.
    /// If the resultant parser is used before this declaration is defined (see `.define`) then a panic will occur.
    pub fn link(&self) -> Parser<'a, T, O, E> {
        let parser = Rc::downgrade(&self.parser);
        Parser::dynamic(move |tokens| {
            (*parser.upgrade().expect("Parser was dropped")).borrow().as_ref().expect("Parser was declared but not defined").f.parse(tokens)
        })
    }

    /// Provider a parser definition for this declaration, thereby sealing it as a well-defined parser.
    pub fn define(self, parser: Parser<'a, T, O, E, impl ParseFn<T, O, E>>) -> Parser<'a, T, O, E> {
        *self.parser.borrow_mut() = Some(parser.to_object());
        Parser::dynamic(move |tokens| (*self.parser).borrow().as_ref().unwrap().f.parse(tokens))
    }
}

/// Declare a parser before defining it. A definition can be given later with the `.define` method.
///
/// This function is generally used to create recursive parsers, along with `call`.
pub fn declare<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a>() -> Declaration<'a, T, O, E> {
    Declaration::default()
}

/// A wrapper function for recursive parser declarations.
///
/// This function uses `Declaration` internally.
pub fn recursive<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a>(f: impl FnOnce(Parser<'a, T, O, E>) -> Parser<'a, T, O, E> + 'a) -> Parser<'a, T, O, E> {
    let p = Declaration::default();
    let p_link = p.link();
    p.define(f(p_link))
}

// Helpers

fn attempt<'a, T: Clone + 'a, R, F, E: ParseError<T> + 'a>(tokens: &mut TokenIter<T>, f: F) -> Result<R, Fail<E>>
    where F: FnOnce(&mut TokenIter<T>) -> Result<R, Fail<E>>,
{
    let mut tokens2 = tokens.clone();
    let tok = f(&mut tokens2)?;
    *tokens = tokens2;
    Ok(tok)
}

fn try_parse<'a, T: Clone + 'a, R, F, E: ParseError<T> + 'a>(tokens: &mut TokenIter<T>, f: F) -> Result<(MayFail<E>, R), Fail<E>>
    where F: FnOnce((usize, T), &mut TokenIter<T>) -> Result<(MayFail<E>, R), Fail<E>>,
{
    attempt(tokens, |tokens| f(tokens.next().ok_or_else(|| Fail::new(!0, E::unexpected_end()))?, tokens))
}

// Utility

/// A parser that accepts the given symbol.
pub fn sym<'b, 'a, T: Clone + 'a, E: ParseError<T> + 'a, U: Clone + 'a>(expected: U) -> Parser<'a, T, T, E, impl ParseFn<T, T, E> + Captures<'b> + 'a>
    where T: PartialEq<U>, 'a: 'b, 'b: 'a
{
    permit(move |tok: T| tok == expected)
}

/// A parser that accepts any one thing that is not the given symbol.
pub fn not_sym<'b, 'a, T: Clone + 'a + PartialEq, E: ParseError<T> + 'a, U: Borrow<T> + Clone + 'a>(expected: U) -> Parser<'a, T, T, E, impl ParseFn<T, T, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    permit(move |tok: T| &tok != expected.borrow())
}

/// A parser that accepts one of the given set of symbols.
pub fn one_of<'b, 'a, T: Clone + 'a + PartialEq, E: ParseError<T> + 'a, U: Borrow<T> + Clone + 'a>(expected: impl IntoIterator<Item=U>) -> Parser<'a, T, T, E, impl ParseFn<T, T, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    let expected = expected.into_iter().collect::<Vec<_>>();
    permit(move |tok| expected.iter().any(|e| &tok == e.borrow()))
}

/// A parser that accepts any one symbol that is not within the given set of symbols.
pub fn none_of<'b, 'a, T: Clone + 'a + PartialEq, E: ParseError<T> + 'a, U: Borrow<T> + Clone + 'a>(unexpected: impl IntoIterator<Item=U>) -> Parser<'a, T, T, E, impl ParseFn<T, T, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    let unexpected = unexpected.into_iter().collect::<Vec<_>>();
    permit(move |tok| unexpected.iter().all(|e| &tok != e.borrow()))
}

/// A parser that accepts all of the given list of symbols, one after another.
pub fn all_of<'b, 'a, T: Clone + 'a + PartialEq, E: ParseError<T> + 'a, U: Borrow<T> + Clone + 'a>(expected: impl IntoIterator<Item=U>) -> Parser<'a, T, Vec<T>, E, impl ParseFn<T, Vec<T>, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    let expected = expected.into_iter().collect::<Vec<_>>();
    Parser::generic(move |tokens| {
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

/// A parser that accepts one symbol provided it passes the given test.
pub fn permit<'b, 'a, T: Clone + 'a, E: ParseError<T> + 'a>(f: impl Fn(T) -> bool + Clone + 'a) -> Parser<'a, T, T, E, impl ParseFn<T, T, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    Parser::try_map(move |tok: T| if f(tok.clone()) { Ok(tok) } else { Err(E::unexpected(tok)) })
}

/// A parser that accepts one symbol provided it passes the given test, mapping it to another symbol in the process.
///
/// This function is extremely powerful, and is actually a superset of several other parser functions defined in this crate.
/// However, this power also makes it fairly awkward to use. You might be better served by another function.
pub fn try_map<'b, 'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a>(f: impl Fn(T) -> Result<O, E> + Clone + 'a) -> Parser<'a, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    Parser::try_map(f)
}

/// A parser that accepts one symbol provided it passes the given test, mapping it to another symbol in the process.
pub fn maybe_map<'b, 'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a>(f: impl Fn(T) -> Option<O> + Clone + 'a) -> Parser<'a, T, O, E, impl ParseFn<T, O, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    Parser::try_map(move |tok: T| f(tok.clone()).ok_or(E::unexpected(tok)))
}

/// A parser that accepts any single symbol.
pub fn any_sym<'b, 'a, T: Clone + 'a, E: ParseError<T> + 'a>() -> Parser<'a, T, T, E, impl ParseFn<T, T, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    permit(|_| true)
}

/// A parser that accepts all input symbols.
pub fn all_sym<'b, 'a, T: Clone + 'a + PartialEq, E: ParseError<T> + 'a>() -> Parser<'a, T, Vec<T>, E, impl ParseFn<T, Vec<T>, E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    permit(|_| true).repeat(..)
}

/// A parser that does not accept any input symbols.
pub fn nothing<'b, 'a, T: Clone + 'a, E: ParseError<T> + 'a>() -> Parser<'a, T, (), E, impl ParseFn<T, (), E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    permit(|_| false).discard()
}

/// A parser that accepts no symbols.
pub fn empty<'b, 'a, T: Clone + 'a + PartialEq, E: ParseError<T> + 'a>() -> Parser<'a, T, (), E, impl ParseFn<T, (), E> + Captures<'b> + 'a>
    where 'a: 'b, 'b: 'a
{
    Parser::generic(|_| Ok((MayFail::none(), ())))
}

/// A parser that accepts any number of 'padding' symbols. Usually, this is taken to mean whitespace.
///
/// You can implement the `Padded` trait for your own symbol types to use this function with them.
pub fn padding<'b, 'a, T: Clone + 'a, U: Padded, E: ParseError<T> + 'a>() -> Parser<'a, T, (), E, impl ParseFn<T, (), E> + Captures<'b> + 'a>
    where T: Borrow<U>, 'a: 'b, 'b: 'a
{
    Parser::generic_raw(|tokens: &mut TokenIter<T>| {
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

/// A parser that invokes another parser, as generated by the given function.
///
/// This function is generally used to create recursive parsers, along with `Declaration`.
pub fn call<'a, T: Clone + 'a, O: 'a, E: ParseError<T> + 'a>(f: impl Fn() -> Parser<'a, T, O, E> + 'a) -> Parser<'a, T, O, E> {
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
        nothing,
        empty,
        permit,
        padding,
        maybe_map,
        try_map,
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

///     bar: Parser<char, _> = {
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


