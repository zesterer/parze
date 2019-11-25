pub trait Chain<N> {
    type Chained;

    fn chain(self, next: N) -> Self::Chained;
}

/*
impl<T> Chain<T> for T {
    type Chained = Vec<T>;

    fn chain(self, next: Self) -> Self::Chained { vec![self, next] }
}
*/

impl<T> Chain<T> for Vec<T> {
    type Chained = Vec<T>;

    fn chain(mut self, next: T) -> Self::Chained {
        self.push(next);
        self
    }
}

impl<T> Chain<Vec<T>> for T {
    type Chained = Vec<T>;

    fn chain(self, mut next: Vec<T>) -> Self::Chained {
        let mut this = vec![self];
        this.append(&mut next);
        this
    }
}

impl<T> Chain<Vec<T>> for Vec<T> {
    type Chained = Vec<T>;

    fn chain(mut self, mut next: Vec<T>) -> Self::Chained {
        self.append(&mut next);
        self
    }
}
