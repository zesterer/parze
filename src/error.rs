/// A trait to be implemented by parser errors.
/// The default implementation of this trait is `DefaultParseError`.
/// You may implement it yourself to have custom errors be generated by the parser.
pub trait ParseError<'a, T: Clone + 'a>: Sized {
    /// Create an error that indicates that the given symbol was not expected by the parser.
    fn unexpected(token: T) -> Self;

    /// Create an error that indicates that the symbol input unexpectedly ended.
    fn unexpected_end() -> Self;

    /// Combine two errors of equal priority
    fn combine(self, _other: Self) -> Self { self }
}

/// The default implementation of `ParseError`.
/// Unless specified, parsers will use this type as their error type.
#[derive(Clone, Debug, PartialEq)]
pub enum DefaultParseError<T> {
    /// A symbol was unexpected.
    Unexpected(T),
    /// The symbol input unexpectedly ended.
    UnexpectedEnd,
}

impl<'a, T: Clone + 'a> ParseError<'a, T> for DefaultParseError<T> {
    fn unexpected(token: T) -> Self {
        DefaultParseError::Unexpected(token)
    }

    fn unexpected_end() -> Self {
        DefaultParseError::UnexpectedEnd
    }
}
