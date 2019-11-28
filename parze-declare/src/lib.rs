#![feature(proc_macro_def_site, proc_macro_quote, proc_macro_hygiene, trait_alias)]

mod rule;
mod expr;

extern crate proc_macro;

use proc_macro::{TokenStream, TokenTree};

#[derive(Debug)]
enum Error {
    UnexpectedToken,
    ExpectedAtom,
    ExpectedPunct,
}

trait TokenStreamExt {
    fn and(self, other: TokenStream) -> TokenStream;
}

impl TokenStreamExt for TokenStream {
    fn and(mut self, other: TokenStream) -> TokenStream {
        self.extend(Some(other));
        self
    }
}

impl TokenStreamExt for TokenTree {
    fn and(self, other: TokenStream) -> TokenStream {
        let mut this = TokenStream::from(self);
        this.extend(Some(other));
        this
    }
}

trait TokenIter = Iterator<Item=TokenTree> + Clone;

fn attempt<'a, 'c: 'a, I, R, E, F>(iter: &mut I, f: F) -> Result<R, E>
    where
        I: TokenIter,
        F: FnOnce(&mut I) -> Result<R, E>,
{
    let mut iter2 = iter.clone();
    let tok = f(&mut iter2)?;
    *iter = iter2;
    Ok(tok)
}

#[proc_macro]
pub fn rule(stream: TokenStream) -> TokenStream {
    rule::parse_rule(&mut stream.into_iter()).unwrap().into()
}
