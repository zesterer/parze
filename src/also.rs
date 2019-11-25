pub trait Also<N> {
    type Alsoed;

    fn also(self, next: N) -> Self::Alsoed;
}

impl<T, U> Also<T> for (U,) {
    type Alsoed = (U, T);
    fn also(self, next: T) -> Self::Alsoed { (self.0, next) }
}

impl<T, U, V> Also<T> for (U, V) {
    type Alsoed = (U, V, T);
    fn also(self, next: T) -> Self::Alsoed { (self.0, self.1, next) }
}

impl<T, U, V, W> Also<T> for (U, V, W) {
    type Alsoed = (U, V, W, T);
    fn also(self, next: T) -> Self::Alsoed { (self.0, self.1, self.2, next) }
}

impl<T, U, V, W, X> Also<T> for (U, V, W, X) {
    type Alsoed = (U, V, W, X, T);
    fn also(self, next: T) -> Self::Alsoed { (self.0, self.1, self.2, self.3, next) }
}

impl<T, U, V, W, X, Y> Also<T> for (U, V, W, X, Y) {
    type Alsoed = (U, V, W, X, Y, T);
    fn also(self, next: T) -> Self::Alsoed { (self.0, self.1, self.2, self.3, self.4, next) }
}

impl<T, U, V, W, X, Y, Z> Also<T> for (U, V, W, X, Y, Z) {
    type Alsoed = (U, V, W, X, Y, Z, T);
    fn also(self, next: T) -> Self::Alsoed { (self.0, self.1, self.2, self.3, self.4, self.5, next) }
}
