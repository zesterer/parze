pub trait Chain {
    type Item;
    type IntoIter: IntoIterator<Item=Self::Item>;
    fn into_iter(self) -> <Self::IntoIter as IntoIterator>::IntoIter;
    fn as_slice(&self) -> &[Self::Item];
}

impl<T> Chain for Vec<T> {
    type Item = T;
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn into_iter(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] { &self }
}

pub(crate) struct Single<T>([T; 1]);

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
    fn into_iter(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] { &self.0 }
}

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
    type Chain = OptionChain<T>;

    fn into_chain(self) -> Self::Chain {
        OptionChain(self.map(|item| [item]))
    }
}

pub struct OptionChain<T>(Option<[T; 1]>);

impl<T> Chain for OptionChain<T> {
    type Item = T;
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn into_iter(self) -> <Self::IntoIter as IntoIterator>::IntoIter { IntoIterator::into_iter(self) }
    fn as_slice(&self) -> &[Self::Item] {
        self.0.as_ref().map(|arr| arr.as_ref()).unwrap_or(&[])
    }
}

impl<T> IntoIterator for OptionChain<T> {
    type Item = T;
    type IntoIter = SingleIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.map(|[inner]| {
            SingleIter(Some(inner))
        }).unwrap_or_else(|| SingleIter(None))
    }
}
