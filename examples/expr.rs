use parze::prelude::*;

#[derive(Debug)]
enum Expr {
    Literal(i64),
    Neg(Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Rem(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn eval(&self) -> i64 {
        match self {
            Expr::Literal(a) => *a,
            Expr::Neg(a) => -a.eval(),
            Expr::Mul(a, b) => a.eval() * b.eval(),
            Expr::Div(a, b) => a.eval() / b.eval(),
            Expr::Rem(a, b) => a.eval() % b.eval(),
            Expr::Add(a, b) => a.eval() + b.eval(),
            Expr::Sub(a, b) => a.eval() - b.eval(),
        }
    }
}

fn main() {
    let expr: Parser<_, _> = recursive(|expr| {
        // Accepts any integer
        let number = (one_of("0123456789".chars()) * (1..)).collect::<String>() % |s| Expr::Literal(s.parse().unwrap());

        // An integer or a parenthesised expression
        let atom = (number | sym('(') >> expr << sym(')')).padded();

        // Any number of unary operators, then an atom
        let unary = (sym('-').padded() * Any + atom)
            .reduce_left(|_, e| Expr::Neg(e.into()));

        // A unary, then any number of product operations
        let product = (unary.clone() + (one_of(&['*', '/', '%']).padded() + unary) * Any)
            .reduce_right(|a, (op, b)| match op {
                '*' => Expr::Mul(a.into(), b.into()),
                '/' => Expr::Div(a.into(), b.into()),
                '%' => Expr::Rem(a.into(), b.into()),
                _ => unreachable!(),
            });

        // A product, then any number of sum operations
        let sum = (product.clone() + (one_of(&['+', '-']).padded() + product) * Any)
            .reduce_right(|a, (op, b)| match op {
                '+' => Expr::Add(a.into(), b.into()),
                '-' => Expr::Sub(a.into(), b.into()),
                _ => unreachable!(),
            });

        sym(' ') * Any >> sum
    });

    assert_eq!(
        expr.parse("14 + 3 / 1 * (2 + 4) + -1".chars().collect::<Vec<_>>()).unwrap().eval(),
        31,
    );
}
