// ReduceLeft

pub trait ReduceLeft<T, U> {
    fn reduce_left(self, f: impl Fn(U, T) -> T) -> T;
}

impl<T, U, I: IntoIterator<Item=U>> ReduceLeft<T, U> for (I, T) {
    fn reduce_left(self, f: impl Fn(U, T) -> T) -> T { self.0.into_iter().fold(self.1, |a, b| f(b, a)) }
}

/*
impl<T, U> ReduceLeft<T, U> for (T, U) {
    fn reduce_left(self, f: impl Fn(U, T) -> T) -> T { f(self.1, self.0) }
}
*/

// ReduceRight

pub trait ReduceRight<T, U> {
    fn reduce_right(self, f: impl Fn(T, U) -> T) -> T;
}

impl<T, U, I: IntoIterator<Item=U>> ReduceRight<T, U> for (T, I) {
    fn reduce_right(self, f: impl Fn(T, U) -> T) -> T { self.1.into_iter().fold(self.0, f) }
}

/*
impl<T, U> ReduceRight<T, U> for (T, U) {
    fn reduce_right(self, f: impl Fn(T, U) -> T) -> T { f(self.0, self.1) }
}
*/
