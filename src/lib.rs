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
//!         | '[' -& bf &- ']' => |ts| { Instr::Loop(ts) }
//!         ) *
//!     }
//! }
//! ```

extern crate alloc;

pub mod error;
pub mod repeat;
pub mod also;
pub mod chain;
pub mod reduce;
mod fail;

use alloc::rc::Rc;
use core::{
    slice,
    iter::{self, FromIterator},
    cell::RefCell,
    borrow::Borrow,
    //ops::{Add, BitOr, Mul, Rem, Sub, Shl, Shr, Not},
};
use crate::{
    error::{ParseError, DefaultParseError},
    repeat::Repeat,
    fail::{Fail, MayFail},
    also::Also,
    chain::Chain,
    reduce::{ReduceLeft, ReduceRight},
};

type TokenIter<'a, T> = iter::Enumerate<iter::Cloned<slice::Iter<'a, T>>>;

/// A type that represents a rule that may be used to parse a list of symbols.
///
/// Parsers may be combined and manipulated in various ways to create new parsers.
pub struct Parser<'a, T: Clone + 'a, O: 'a = T, E: ParseError<'a, T> + 'a = DefaultParseError<T>> {
    f: Rc<dyn Fn(&mut TokenIter<T>) -> Result<(MayFail<E>, O), Fail<E>> + 'a>,
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

    // Create a parser that accepts input symbols according to the given custom rule.
    //
    // This is rarely useful. Before use, consider whether other functions may better fit your requirements.
    fn custom(f: impl Fn(&mut TokenIter<T>) -> Result<(MayFail<E>, O), Fail<E>> + 'a) -> Self {
        Self { f: Rc::new(move |tokens| attempt(tokens, &f)) }
    }

    fn maybe_map(f: impl Fn(T) -> Option<O> + 'a) -> Self {
        Self::custom(move |tokens| try_parse(tokens, |(idx, tok), _| {
            match f(tok.clone()) {
                Some(output) => Ok((MayFail::none(), output)),
                None => Err(Fail::new(idx, E::unexpected(tok))),
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
    pub fn then<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, (O, U), E> {
        Parser::custom(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            let (b_fail, b) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), (a, b)))
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    ///
    /// Whereas `.then` turns outputs of `(T, U)` and `V` into `((T, U), V)`, this method turns them into `(T, U, V)`.
    /// Due to current limitations in Rust's type system, this method is significantly less useful than it could be.
    pub fn also<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, O::Alsoed, E> where O: Also<U> {
        Parser::custom(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            let (b_fail, b) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), a.also(b)))
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser.
    ///
    /// Unlike `.then`, this method will chain the two parser outputs together as a vector.
    pub fn chain<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, O::Chained, E> where O: Chain<U> {
        self.then(other).map(|(a, b)| a.chain(b))
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of this parser.
    pub fn delimiter_for<U: 'a>(self, other: Parser<'a, T, U, E>) -> Parser<'a, T, U, E> {
        Parser::custom(move |tokens| {
            let (a_fail, _) = (self.f)(tokens)?;
            let (b_fail, b) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), b))
        })
    }

    /// Create a parser that parses symbols that match this parser and then another parser, discarding the output of the other parser.
    pub fn delimited_by<U: 'a>(self, other: Parser<'a, T, U, E>) -> Self {
        Parser::custom(move |tokens| {
            let (a_fail, a) = (self.f)(tokens)?;
            let (b_fail, _) = (other.f)(tokens)?;
            Ok((a_fail.max(b_fail), a))
        })
    }

    /// Create a parser that parses symbols that match this parser followed by any number of the given symbol.
    pub fn padded_by(self, padding: impl Borrow<T> + 'a) -> Self where T: PartialEq {
        self.delimited_by(sym(padding).repeat(..))
    }

    /// Create a parser that parses character-like symbols that match this parser followed by any number of whitespace symbols.
    pub fn padded(self) -> Self where T: Borrow<char> {
        self.delimited_by(permit(|c: T| c.borrow().is_whitespace()).repeat(..))
    }

    /// Create a parser that parses symbols that match this parser or another parser.
    pub fn or(self, other: Parser<'a, T, O, E>) -> Self {
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

    /// Create a parser that parses symbols that match this parser or another fallback parser, prioritising errors from this parser.
    ///
    /// This method is 'short-circuiting': if this parser succeeds, the fallback parser won't even be invoked.
    /// This means that emitted errors may not include information from the fallback parser.
    pub fn or_fallback(self, other: Parser<'a, T, O, E>) -> Self {
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

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Declaration<'a, T, O, E> {
    /// Create a new parser declaration.
    pub fn new() -> Self {
        Self { parser: Rc::new(RefCell::new(None)) }
    }

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
    Declaration::new()
}

/// A wrapper function for recursive parser declarations.
///
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
pub fn maybe_map<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a>(f: impl Fn(T) -> Option<O> + 'static) -> Parser<'a, T, O, E> {
    Parser::maybe_map(f)
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
        maybe_map,
        call,
        rule,
        parsers,
    };
}

#[macro_export]
macro_rules! parze_error {
    () => {};
}

#[macro_export]
macro_rules! rule {
    // Atoms

    ( ( $($inner:tt)* ) ) => { ($crate::rule!( $($inner)* )) };
    ( { $($inner:tt)* } ) => { { $($inner)* } };
    ( [ $inner:tt ] ) => { { $crate::all_of($crate::rule!(@AS_EXPR $inner)) } };

    // Tailed atoms

    ( @AS_EXPR $x:tt $($tail:tt)* ) => { $crate::rule!( { $x } $($tail)* ) };
    ( $x:literal $($tail:tt)* ) => { $crate::rule!( { $crate::sym($x) } $($tail)* ) };
    //( $x:ident ( $($inner:tt)* ) $($tail:tt)* ) => { $crate::rule!( { $x($($inner)*) } $($tail)* ) };
    ( $x:ident $($tail:tt)* ) => { $crate::rule!( { $x.link() } $($tail)* ) };

    // Mapping and methods

    ( $a:tt -> $b:tt $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).to($crate::rule!(@AS_EXPR $b)) } $($tail)*)
    };
    ( $a:tt => | $kind:pat | $b:tt $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).map(|$kind| $crate::rule!(@AS_EXPR $b)) } $($tail)*)
    };
    ( $a:tt . $method:ident ( $($args:tt)* ) $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).$method($($args)*) } $($tail)*)
    };

    // High-precedence operators

    ( $a:tt -& $b:tt $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).delimiter_for($crate::rule!($b)) } $($tail)*)
    };
    ( $a:tt &- $b:tt $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).delimited_by($crate::rule!($b)) } $($tail)*)
    };
    ( $a:tt & $b:tt $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).then($crate::rule!($b)) } $($tail)*)
    };

    // Repetition

    ( $a:tt *= $b:tt $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).repeat($crate::rule!(@AS_EXPR $b)) } $($tail)*)
    };
    ( $a:tt * $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).repeat(..) } $($tail)*)
    };
    ( $a:tt + $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).repeat(1..) } $($tail)*)
    };
    ( $a:tt ? $($tail:tt)* ) => {
        $crate::rule!({ ($crate::rule!($a)).or_not() } $($tail)*)
    };

    // Low-precedence operators

    ( $a:tt | $($b:tt)* ) => {
        { ($crate::rule!($a)).or($crate::rule!($($b)*)) }
    };

    // Ignore prefix operators

    ( | $($a:tt)* ) => {
        $crate::rule!($($a)*)
    };
    ( & $($a:tt)* ) => {
        $crate::rule!($($a)*)
    };

    ( $x:tt ) => { $x };

    ( $($tail:tt)* ) => {
        $crate::parze_error!($($tail)*);
    };
}

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


