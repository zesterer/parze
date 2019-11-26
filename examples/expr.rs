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
    parsers! {
        number = {
            { one_of("0123456789".chars()) }+ => { |s| Expr::Literal(s.into_iter().collect::<String>().parse().unwrap()) }
        }

        atom = {
            ( number | '(' -& expr &- ')').padded()
        }

        unary = {
            ('-'.padded()* & atom).reduce_left(|_, e| Expr::Neg(e.into()))
        }

        product = {
            (unary & ((('*' | '/' | '%').padded() & unary)*)).reduce_right(|a, (op, b)| match op {
                '*' => Expr::Mul(a.into(), b.into()),
                '/' => Expr::Div(a.into(), b.into()),
                '%' => Expr::Rem(a.into(), b.into()),
                _ => unreachable!(),
            })
        }

        sum = {
            (product & ((('+' | '-').padded() & product)*)).reduce_right(|a, (op, b)| match op {
                '+' => Expr::Add(a.into(), b.into()),
                '-' => Expr::Sub(a.into(), b.into()),
                _ => unreachable!(),
            })
        }

        expr: Parser<_, _> = { ' '* -& sum }
    }

    assert_eq!(
        expr.parse("14 + 3 / 1 * (2 + 4) + -1".chars().collect::<Vec<_>>()).unwrap().eval(),
        31,
    );
}
