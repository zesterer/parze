use core::marker::PhantomData;
use alloc::rc::Rc;
use crate::{
    ParseError,
    ParseResult,
    TokenIter,
    chain::{IntoChain, Chain, Single},
};

pub trait ParseFn<T: Clone, O, E: ParseError<T>>: Clone {
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E>;
}

// RcParseFn

pub struct RcParseFn<'a, T: Clone, O, E: ParseError<T>> {
    parse: Rc<dyn Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a>,
}

impl<'a, T: Clone, O, E: ParseError<T>> RcParseFn<'a, T, O, E> {
    pub fn new(f: impl Fn(&mut TokenIter<T>) -> ParseResult<O, E> + 'a) -> Self {
        Self { parse: Rc::new(f) }
    }
}

impl<T: Clone, O, E: ParseError<T>> Clone for RcParseFn<'_, T, O, E> {
    fn clone(&self) -> Self {
        Self { parse: self.parse.clone() }
    }
}

impl<T: Clone, O, E: ParseError<T>> ParseFn<T, O, E> for RcParseFn<'_, T, O, E> {
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E> {
        (self.parse)(tokens)
    }
}

// GenParseFn

pub struct GenParseFn<T: Clone, O, E: ParseError<T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone> {
    parse: F,
    _phantom: PhantomData<(T, O, E)>,
}

impl<T: Clone, O, E: ParseError<T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone> GenParseFn<T, O, E, F> {
    pub fn new(f: F) -> Self {
        Self {
            parse: f,
            _phantom: PhantomData,
        }
    }
}

impl<T: Clone, O, E: ParseError<T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone> Clone for GenParseFn<T, O, E, F> {
    fn clone(&self) -> Self {
        Self {
            parse: self.parse.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<T: Clone, O, E: ParseError<T>, F: Fn(&mut TokenIter<T>) -> ParseResult<O, E> + Clone> ParseFn<T, O, E> for GenParseFn<T, O, E, F> {
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E> {
        (self.parse)(tokens)
    }
}

// ThenFn

#[derive(Clone)]
pub(crate) struct ThenFn<A, B>(pub A, pub B);

impl<T, O, U, E, F, G> ParseFn<T, Single<(O, U)>, E> for ThenFn<F, G>
    where
        T: Clone,
        E: ParseError<T>,
        F: ParseFn<T, O, E>,
        G: ParseFn<T, U, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<Single<(O, U)>, E> {
        let (a_fail, a) = self.0.parse(tokens)?;
        match self.1.parse(tokens) {
            Ok((b_fail, b)) => Ok((a_fail.max(b_fail), (a, b).into())),
            Err(b_fail) => Err(b_fail.max(a_fail)),
        }
    }
}

// AlsoFn

/*
#[derive(Clone)]
pub(crate) struct AlsoFn<A, B>(pub A, pub B);

impl<T, O, U, E, F, G> ParseFn<T, Single<(O, U)>, E> for AlsoFn<F, G>
    where
        T: Clone,
        E: ParseError<T>,
        F: ParseFn<T, Single<O>, E>,
        G: ParseFn<T, Single<U>, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<Single<(O, U)>, E> {
        let (a_fail, a) = self.0.parse(tokens)?;
        match self.1.parse(tokens) {
            Ok((b_fail, b)) => Ok((a_fail.max(b_fail), (a.into_inner(), b.into_inner()).into())),
            Err(b_fail) => Err(b_fail.max(a_fail)),
        }
    }
}
*/

#[derive(Clone)]
pub(crate) struct AlsoFn<A, B>(pub A, pub B);

impl<T, O, U, E, F, G> ParseFn<T, Single<(O, U)>, E> for AlsoFn<F, G>
    where
        T: Clone,
        E: ParseError<T>,
        F: ParseFn<T, O, E>,
        G: ParseFn<T, U, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<Single<(O, U)>, E> {
        let (a_fail, a) = self.0.parse(tokens)?;
        match self.1.parse(tokens) {
            Ok((b_fail, b)) => Ok((a_fail.max(b_fail), (a, b).into())),
            Err(b_fail) => Err(b_fail.max(a_fail)),
        }
    }
}

// ChainFn

pub(crate) struct ChainFn<A, B, O, U>(pub A, pub B, pub PhantomData<(O, U)>);

impl<A: Clone, B: Clone, O, U> Clone for ChainFn<A, B, O, U> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone(), PhantomData)
    }
}

impl<T, O, U, V, E, F, G> ParseFn<T, Vec<V>, E> for ChainFn<F, G, O, U>
    where
        T: Clone,
        O: IntoChain<Item=V>,
        U: IntoChain<Item=V>,
        E: ParseError<T>,
        F: ParseFn<T, O, E>,
        G: ParseFn<T, U, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<Vec<V>, E> {
        let (a_fail, a) = self.0.parse(tokens)?;
        match self.1.parse(tokens) {
            Ok((b_fail, b)) => Ok((a_fail.max(b_fail), a.into_chain().into_iter_chain().chain(b.into_chain().into_iter_chain()).collect::<Vec<_>>())),
            Err(b_fail) => Err(b_fail.max(a_fail)),
        }
    }
}

// OrFallbackFn

#[derive(Clone)]
pub(crate) struct OrFallbackFn<A, B>(pub A, pub B);

impl<T, O, E, F, G> ParseFn<T, O, E> for OrFallbackFn<F, G>
    where
        T: Clone,
        E: ParseError<T>,
        F: ParseFn<T, O, E>,
        G: ParseFn<T, O, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<O, E> {
        let a = self.0.parse(tokens);
        match a {
            Ok((a_fail, a)) => Ok((a_fail, a)),
            Err(a_fail) => match self.1.parse(tokens) {
                Ok((b_fail, b)) => Ok((b_fail.max(a_fail), b)),
                Err(b_fail) => Err(a_fail.max(b_fail)),
            },
        }
    }
}


// OrFn

pub struct OrFn<A, B, O, U>(pub A, pub B, pub PhantomData<(O, U)>);

impl<A: Clone, B: Clone, O, U> Clone for OrFn<A, B, O, U> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone(), PhantomData)
    }
}

impl<T, O, U, V, E, F, G> ParseFn<T, Vec<V>, E> for OrFn<F, G, O, U>
    where
        T: Clone,
        O: IntoChain<Item=V>,
        U: IntoChain<Item=V>,
        E: ParseError<T>,
        F: ParseFn<T, O, E>,
        G: ParseFn<T, U, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<Vec<V>, E> {
        let a = self.0.parse(tokens);
        let mut b_tokens = tokens.clone();
        let b = self.1.parse(&mut b_tokens);
        match a {
            Ok((a_fail, a)) => match b {
                Ok((b_fail, _)) => Ok((a_fail.max(b_fail), a.into_chain().into_iter_chain().collect::<Vec<_>>())),
                Err(b_fail) => Ok((a_fail.max(b_fail), a.into_chain().into_iter_chain().collect::<Vec<_>>())),
            },
            Err(a_fail) => match b {
                Ok((b_fail, b)) => {
                    *tokens = b_tokens;
                    Ok((b_fail.max(a_fail), b.into_chain().into_iter_chain().collect::<Vec<_>>()))
                },
                Err(b_fail) => Err(a_fail.max(b_fail)),
            },
        }
    }
}

// OrChainFallbackFn

pub struct OrChainFallbackFn<A, B, O, U>(pub A, pub B, pub PhantomData<(O, U)>);

impl<A: Clone, B: Clone, O, U> Clone for OrChainFallbackFn<A, B, O, U> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone(), PhantomData)
    }
}

impl<T, O, U, V, E, F, G> ParseFn<T, Vec<V>, E> for OrChainFallbackFn<F, G, O, U>
    where
        T: Clone,
        O: IntoChain<Item=V>,
        U: IntoChain<Item=V>,
        E: ParseError<T>,
        F: ParseFn<T, O, E>,
        G: ParseFn<T, U, E>,
{
    fn parse(&self, tokens: &mut TokenIter<T>) -> ParseResult<Vec<V>, E> {
        let a = self.0.parse(tokens);
        match a {
            Ok((a_fail, a)) => Ok((a_fail, a.into_chain().into_iter_chain().collect::<Vec<_>>())),
            Err(a_fail) => match self.1.parse(tokens) {
                Ok((b_fail, b)) => Ok((b_fail.max(a_fail), b.into_chain().into_iter_chain().collect::<Vec<_>>())),
                Err(b_fail) => Err(a_fail.max(b_fail)),
            },
        }
    }
}
