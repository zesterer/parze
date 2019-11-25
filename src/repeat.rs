use std::ops::{Range, RangeFull, RangeFrom, RangeTo};

/// A type that represents possible pattern repetitions.
#[derive(Copy, Clone)]
pub enum Repeat {
    /// The pattern may be seen any number of times (including not at all).
    Any,
    /// The pattern must be seen a specific number of times.
    Exactly(usize),
    /// The pattern must be seen at least a specific number of times.
    AtLeast(usize),
    /// The pattern must be seen at most a specific number of times.
    AtMost(usize),
    /// The pattern must be seen at least a specific number of times and at most a specific number of times.
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
    /// Returns true if this repetition permits the given number of repetitions.
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
