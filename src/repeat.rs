use std::ops::{Range, RangeFull, RangeFrom, RangeTo};

#[derive(Copy, Clone)]
pub enum Repeat {
    Any,
    Exactly(usize),
    AtLeast(usize),
    AtMost(usize),
    Range(usize, usize),
}

impl From<usize> for Repeat {
    fn from(n: usize) -> Self {
        Repeat::Exactly(n)
    }
}

impl From<RangeFull> for Repeat {
    fn from(_: RangeFull) -> Self {
        Repeat::Any
    }
}

impl From<Range<usize>> for Repeat {
    fn from(from: Range<usize>) -> Self {
        Repeat::Range(from.start, from.end)
    }
}

impl From<RangeFrom<usize>> for Repeat {
    fn from(from: RangeFrom<usize>) -> Self {
        Repeat::AtLeast(from.start)
    }
}

impl From<RangeTo<usize>> for Repeat {
    fn from(from: RangeTo<usize>) -> Self {
        Repeat::AtMost(from.end)
    }
}

impl Repeat {
    pub fn contains(self, m: usize) -> bool {
        match self {
            Repeat::Any => true,
            Repeat::Exactly(n) if m == n => true,
            Repeat::AtLeast(n) if m >= n => true,
            Repeat::AtMost(n) if m <= n => true,
            Repeat::Range(a, b) if m >= a && m <= b => true,
            _ => false,
        }
    }

    pub(crate) fn idx_upper_limit(self) -> usize {
        match self {
            Repeat::Any => !0,
            Repeat::Exactly(n) => n,
            Repeat::AtLeast(_) => !0,
            Repeat::AtMost(n) => n,
            Repeat::Range(_, b) => b,
        }
    }
}
