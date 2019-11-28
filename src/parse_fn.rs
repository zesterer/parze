use std::{
    rc::Rc,
    marker::PhantomData,
};
use crate::{
    ParseError,
    ParseResult,
    TokenIter,
};

pub trait ParseFn<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>>: Clone {
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E>;
}

/// A Dynamically-allocated internal parser implementation
pub struct RcParseFn<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>> {
    parse: Rc<dyn Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>> RcParseFn<'a, T, O, E> {
    pub fn new(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a) -> Self {
        Self { parse: Rc::new(f) }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> Clone for RcParseFn<'a, T, O, E> {
    fn clone(&self) -> Self {
        Self { parse: self.parse.clone() }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T> + 'a> ParseFn<'a, T, O, E> for RcParseFn<'a, T, O, E> {
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E> {
        (self.parse)(tokens)
    }
}

/// A Dynamically-allocated internal parser implementation
pub struct GenParseFn<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone + 'a> {
    parse: F,
    _phantom: PhantomData<&'a (T, O, E)>,
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone + 'a> GenParseFn<'a, T, O, E, F> {
    pub fn new(f: F) -> Self {
        Self {
            parse: f,
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone + 'a> Clone for GenParseFn<'a, T, O, E, F> {
    fn clone(&self) -> Self {
        Self {
            parse: self.parse.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: Clone + 'a, O: 'a, E: ParseError<'a, T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone + 'a> ParseFn<'a, T, O, E> for GenParseFn<'a, T, O, E, F> {
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E> {
        (self.parse)(tokens)
    }
}
