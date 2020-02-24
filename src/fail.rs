use crate::error::ParseError;

#[derive(Debug)]
pub struct Fail<E>(usize, E);

impl<E> Fail<E> {
    pub fn new(idx: usize, err: E) -> Self {
        Self(idx, err)
    }

    pub fn take_error(self) -> E {
        self.1
    }

    pub fn map_err<G>(self, f: impl Fn(E) -> G) -> Fail<G> {
        Fail(self.0, f(self.1))
    }

    #[inline(always)]
    pub fn max<T: Clone>(self, other: impl Into<MayFail<E>>) -> Self where E: ParseError<T> {
        match other.into().0 {
            Some((idx, err)) if idx > self.0 => Self(idx, err),
            Some((idx, _)) if idx < self.0 => Self(self.0, self.1),
            Some((idx, err)) if idx == self.0 => Self(idx, err.combine(self.1)),
            _ => self,
        }
    }
}

#[derive(Debug)]
pub struct MayFail<E>(Option<(usize, E)>);

impl<E> MayFail<E> {
    pub fn none() -> Self {
        Self(None)
    }

    pub fn map_err<G>(self, f: impl Fn(E) -> G) -> MayFail<G> {
        MayFail(self.0.map(|(idx, e)| (idx, f(e))))
    }

    #[inline(always)]
    pub fn max<T: Clone>(self, other: impl Into<MayFail<E>>) -> Self where E: ParseError<T> {
        match (self.0, other.into().0) {
            (Some(a), Some(b)) => Fail(a.0, a.1).max(Fail(b.0, b.1)).into(),
            (Some((a_idx, a)), _) => Self(Some((a_idx, a))),
            (_, Some((b_idx, b))) => Self(Some((b_idx, b))),
            _ => Self(None),
        }
    }
}

impl<E> From<Fail<E>> for MayFail<E> {
    fn from(fail: Fail<E>) -> Self {
        Self(Some((fail.0, fail.1)))
    }
}
