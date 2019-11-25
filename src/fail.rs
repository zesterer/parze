pub struct Fail<E>(usize, E);

impl<E> Fail<E> {
    pub fn new(idx: usize, err: E) -> Self {
        Self(idx, err)
    }

    pub fn take_error(self) -> E {
        self.1
    }

    pub fn max(self, other: impl Into<MayFail<E>>) -> Self {
        match other.into().0 {
            Some((idx, err)) if idx > self.0 => Self(idx, err),
            _ => self,
        }
    }
}

pub struct MayFail<E>(Option<(usize, E)>);

impl<E> MayFail<E> {
    pub fn none() -> Self {
        Self(None)
    }

    pub fn max(self, other: impl Into<MayFail<E>>) -> Self {
        match (self.0, other.into().0) {
            (Some((a_idx, a)), Some((b_idx, _)))
                if a_idx >= b_idx => Self(Some((a_idx, a))),
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
