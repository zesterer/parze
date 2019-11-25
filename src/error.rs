pub trait ParseError<'a, T: Clone + 'a>: Sized {
    fn unexpected(token: T) -> Self;
    fn unexpected_end() -> Self;
    /// Combine two errors of equal priority
    fn combine(self, _other: Self) -> Self { self }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DefaultParseError<'a, T: Clone + 'a> {
    Unexpected(T),
    UnexpectedEnd,

    _Unused(std::marker::PhantomData<&'a ()>),
}

impl<'a, T: Clone + 'a> ParseError<'a, T> for DefaultParseError<'a, T> {
    fn unexpected(token: T) -> Self {
        DefaultParseError::Unexpected(token)
    }

    fn unexpected_end() -> Self {
        DefaultParseError::UnexpectedEnd
    }
}
