use proc_macro::{
    TokenStream,
    TokenTree,
    Group,
    Delimiter,
    quote,
};
use crate::TokenStreamExt;

#[derive(Debug)]
pub enum Error {
    UnexpectedToken,
    ExpectedAtom,
    ExpectedPunct,
}

pub trait TokenIter = Iterator<Item=TokenTree> + Clone;

fn group_tree(delim: Delimiter, items: TokenStream) -> TokenTree {
    TokenTree::Group(Group::new(delim, items))
}

fn sym(tt: TokenTree) -> TokenTree {
    group_tree(Delimiter::Parenthesis, quote!(parze::prelude::sym).and(group_tree(Delimiter::Parenthesis, tt.into()).into()))
}

fn link(tt: TokenTree) -> TokenTree {
    group_tree(Delimiter::Parenthesis, group_tree(Delimiter::Parenthesis, tt.into()).and(quote!(.link())))
}

fn parse_punct<'a>(stream: &mut impl TokenIter, puncts: &[&'a str]) -> Result<&'a str, Error> {
    attempt(stream, |stream| {
        for punct in puncts {
            match attempt(stream, |stream| {
                for c in punct.chars() {
                    match stream.next().ok_or(Error::ExpectedPunct)? {
                        TokenTree::Punct(punct) if punct.as_char() == c => {}, // TODO: Check joining
                        _ => return Err(Error::ExpectedPunct),
                    }
                }
                Ok(())
            }) {
                Ok(()) => return Ok(*punct),
                Err(_) => {},
            }
        }
        Err(Error::ExpectedPunct)
    })
}

fn parse_atom(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    attempt(stream, |stream| {
        let tt = stream.next().ok_or(Error::ExpectedAtom)?;
        match &tt {
            // Parze expression
            TokenTree::Group(group) if group.delimiter() == Delimiter::Parenthesis
                => parse_rule(&mut group.stream().into_iter()),
            // Embedded Rust expressions
            TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => Ok(tt),
            TokenTree::Literal(_) => Ok(sym(tt)),
            TokenTree::Ident(_) => Ok(link(tt)),
            _ => Err(Error::ExpectedAtom),
        }
    })
}

fn parse_atom_expr(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    attempt(stream, |stream| {
        let tt = stream.next().ok_or(Error::ExpectedAtom)?;
        match &tt {
            TokenTree::Group(_) => Ok(tt),
            TokenTree::Literal(_) => Ok(tt),
            TokenTree::Ident(_) => Ok(tt),
            _ => Err(Error::ExpectedAtom),
        }
    })
}

fn parse_unary_suffix<I: TokenIter, P>(
    stream: &mut I,
    mut parse_item: impl FnMut(&mut I) -> Result<TokenTree, Error>,
    mut parse_op: impl FnMut(&mut I) -> Result<P, Error>,
    combine: &mut impl FnMut(TokenTree, P) -> TokenTree,
) -> Result<TokenTree, Error> {
    attempt(stream, |stream| {
        let mut expr = parse_item(stream)?;

        while let Ok(op) = parse_op(stream) {
            expr = combine(expr, op);
        }

        Ok(expr)
    })
}

fn parse_repeated(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    parse_unary_suffix(
        stream,
        parse_atom,
        |stream| parse_punct(stream, &["?", "+", "*", "~", ".%", ".#"]),
        &mut |item, op| group_tree(
            Delimiter::Parenthesis,
            group_tree(Delimiter::Parenthesis, item.into())
                .and(match op {
                    "?" => quote!(.or_not()),
                    "+" => quote!(.repeat(1..)),
                    "*" => quote!(.repeat(..)),
                    "~" => quote!(.before_padding()),
                    ".%" => quote!(.chained()),
                    ".#" => quote!(.flatten()),
                    _ => unreachable!(),
                })
        ),
    )
}

fn parse_unary_prefix<I: TokenIter, P>(
    stream: &mut I,
    mut parse_item: impl FnMut(&mut I) -> Result<TokenTree, Error>,
    mut parse_op: impl FnMut(&mut I) -> Result<P, Error>,
    combine: &mut impl FnMut(P, TokenTree) -> TokenTree,
) -> Result<TokenTree, Error> {
    attempt(stream, |stream| {
        match parse_op(stream) {
            Ok(op) => {
                let item = parse_unary_prefix(stream, parse_item, parse_op, combine)?;
                Ok(combine(op, item))
            },
            Err(_) => parse_item(stream),
        }
    })
}

fn parse_unary_or(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    parse_unary_prefix(
        stream,
        parse_repeated,
        |stream| parse_punct(stream, &["|", "~"]),
        // Ignore '|' in unary prefix position
        &mut |op, item| group_tree(
            Delimiter::Parenthesis,
            group_tree(Delimiter::Parenthesis, item.into())
                .and(match op {
                    "|" => quote!(), // Ignore '|' in unary prefix position
                    "~" => quote!(.after_padding()),
                    _ => unreachable!(),
                })
        ),
    )
}

fn parse_binary<I: TokenIter, P>(
    stream: &mut I,
    mut parse_item: impl FnMut(&mut I) -> Result<TokenTree, Error>,
    mut parse_tail: impl FnMut(&mut I) -> Result<TokenTree, Error>,
    mut parse_op: impl FnMut(&mut I) -> Result<P, Error>,
    mut combine: impl FnMut(TokenTree, P, TokenTree) -> TokenTree,
) -> Result<TokenTree, Error> {
    attempt(stream, |stream| {
        let mut expr = parse_item(stream)?;

        loop {
            let op = match parse_op(stream) {
                Ok(op) => op,
                Err(_) => break Ok(expr),
            };

            let tail = parse_tail(stream)?;

            expr = combine(expr, op, tail);
        }
    })
}

fn parse_separated(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    parse_binary(
        stream,
        parse_unary_or,
        parse_unary_or,
        |stream| parse_punct(stream, &["..."]),
        |a, op, b| group_tree(
            Delimiter::Parenthesis,
            group_tree(Delimiter::Parenthesis, a.into())
                .and(match op {
                    "..." => quote!(.separated_by),
                    _ => unreachable!(),
                })
                .and(group_tree(Delimiter::Parenthesis, b.into()).into())
        ),
    )
}

fn parse_then(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    parse_binary(
        stream,
        parse_separated,
        parse_separated,
        |stream| parse_punct(stream, &["%", "-&", "&-", "&", "|%"]),
        |a, op, b| group_tree(
            Delimiter::Parenthesis,
            group_tree(Delimiter::Parenthesis, a.into())
                .and(match op {
                    "%" => quote!(.chain),
                    "-&" => quote!(.delimiter_for),
                    "&-" => quote!(.delimited_by),
                    "&" => quote!(.then),
                    "|%" => quote!(.or_chain),
                    _ => unreachable!(),
                })
                .and(group_tree(Delimiter::Parenthesis, b.into()).into())
        ),
    )
}

fn parse_mapping(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    parse_binary(
        stream,
        parse_then,
        parse_atom_expr,
        |stream| parse_punct(stream, &["=>", "->", "<:", ":>"]),
        |a, op, b| group_tree(
            Delimiter::Parenthesis,
            group_tree(Delimiter::Parenthesis, a.into())
                .and(match op {
                    "=>" => quote!(.map),
                    "->" => quote!(.to),
                    "<:" => quote!(.reduce_left),
                    ":>" => quote!(.reduce_right),
                    _ => unreachable!(),
                })
                .and(group_tree(Delimiter::Parenthesis, b.into()).into())
        ),
    )
}

fn parse_or(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    parse_binary(
        stream,
        parse_mapping,
        parse_mapping,
        |tokens| parse_punct(tokens, &["|"]),
        |a, _, b| group_tree(
            Delimiter::Parenthesis,
            group_tree(Delimiter::Parenthesis, a.into())
                .and(quote!(.or))
                .and(group_tree(Delimiter::Parenthesis, b.into()).into())
        ),
    )
}

pub fn parse_rule(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
    let result = parse_or(stream)?;
    match stream.next() {
        Some(_) => Err(Error::UnexpectedToken),
        None => Ok(result),
    }
}

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
