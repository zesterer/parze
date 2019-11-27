#![feature(proc_macro_def_site, proc_macro_quote, proc_macro_hygiene, trait_alias)]

mod rule;

extern crate proc_macro;

use proc_macro::{TokenStream, TokenTree};

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

#[proc_macro]
pub fn rule(stream: TokenStream) -> TokenStream {
    rule::parse_rule(&mut stream.into_iter()).unwrap().into()
}
