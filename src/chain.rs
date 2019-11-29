use core::{
    iter::FromIterator,
    marker::PhantomData,
};

pub trait Chain: Sized {
    type Item;
    type IntoIter: IntoIterator<Item=Self::Item>;
    fn into_iter_chain(self) -> <Self::IntoIter as IntoIterator>::IntoIter;
    fn collect<T: FromIterator<Self::Item>>(self) -> T { self.into_iter_chain().collect() }
    fn as_slice(&self) -> &[Self::Item];
}

impl<T> Chain for Vec<T> {
    type Item = T;
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn into_iter_chain(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] { &self }
}

// Nothing

pub struct Nothing<T>(PhantomData<T>);

impl<T> Nothing<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<T> IntoIterator for Nothing<T> {
    type Item = T;
    type IntoIter = SingleIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        SingleIter(None)
    }
}

impl<T> Chain for Nothing<T> {
    type Item = T;
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn into_iter_chain(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] { &[] }
}

// Single

pub struct Single<T>([T; 1]);

impl<T> Single<T> {
    pub fn into_inner(self) -> T {
        let [inner] = self.0;
        inner
    }
}

impl<T> From<T> for Single<T> {
    fn from(item: T) -> Self {
        Self([item])
    }
}

impl<T> IntoIterator for Single<T> {
    type Item = T;
    type IntoIter = SingleIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let [inner] = self.0;
        SingleIter(Some(inner))
    }
}

impl<T> Chain for Single<T> {
    type Item = T;
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn into_iter_chain(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] { &self.0 }
}

// SingleIter

pub struct SingleIter<T>(Option<T>);

impl<T> Iterator for SingleIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.take()
    }
}

pub trait IntoChain {
    type Item;
    type Chain: Chain<Item=Self::Item>;

    fn into_chain(self) -> Self::Chain;
}

impl<U: Chain> IntoChain for U {
    type Item = U::Item;
    type Chain = Self;
    fn into_chain(self) -> Self::Chain { self }
}

impl<T> IntoChain for Option<T> {
    type Item = T;
    type Chain = Optional<T>;

    fn into_chain(self) -> Self::Chain {
        Optional(self.map(|item| [item]))
    }
}

// Optional

pub struct Optional<T>(Option<[T; 1]>);

impl<T> Optional<T> {
    pub fn some(item: T) -> Self {
        Self(Some([item]))
    }

    pub fn none() -> Self {
        Self(None)
    }
}

impl<T> Chain for Optional<T> {
    type Item = T;
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn into_iter_chain(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] {
        self.0.as_ref().map(|arr| arr.as_ref()).unwrap_or(&[])
    }
}

impl<T> IntoIterator for Optional<T> {
    type Item = T;
    type IntoIter = SingleIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.map(|[inner]| {
            SingleIter(Some(inner))
        }).unwrap_or_else(|| SingleIter(None))
    }
}
