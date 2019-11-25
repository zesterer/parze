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
        let number = (one_of("0123456789".chars()) * (1..)) % |chars| Expr::Literal(chars.into_iter().collect::<String>().parse().unwrap());

        let atom = number.padded_by(' ') | sym('(') >> expr << sym(')').padded_by(' ');

        let unary = (sym('-').padded_by(' ') * Any + atom) % |(ops, expr)| ops.into_iter().fold(expr, |expr, _| Expr::Neg(expr.into()));

        let product = (unary.clone() + (one_of(&['*', '/', '%']).padded_by(' ') + unary) * Any) % |(head, tail)| tail.into_iter().fold(head, |a, (op, b)| match op {
            '*' => Expr::Mul(a.into(), b.into()),
            '/' => Expr::Div(a.into(), b.into()),
            '%' => Expr::Rem(a.into(), b.into()),
            _ => unreachable!(),
        });

        let sum = (product.clone() + (one_of(&['+', '-']).padded_by(' ') + product) * Any) % |(head, tail)| tail.into_iter().fold(head, |a, (op, b)| match op {
            '+' => Expr::Add(a.into(), b.into()),
            '-' => Expr::Sub(a.into(), b.into()),
            _ => unreachable!(),
        });

        sym(' ') * Any >> sum
    });

    println!("{}", expr.parse("14 + 3 * (2 + 4) + -1".chars().collect::<Vec<_>>()).unwrap().eval());
}
