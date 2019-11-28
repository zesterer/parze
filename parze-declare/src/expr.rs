use proc_macro::TokenTree;
use crate::{
    TokenIter,
    Error,
    attempt,
};

pub(crate) fn parse_atom_expr(stream: &mut impl TokenIter) -> Result<TokenTree, Error> {
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
