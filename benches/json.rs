#![feature(test)]

extern crate test;

use std::collections::HashMap;
use test::{Bencher, black_box};

#[derive(Debug, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<JsonValue>),
    Object(HashMap<String,JsonValue>)
}

#[bench]
fn pom(b: &mut Bencher) {
    let json = pom::json();
    b.iter(|| black_box(json.parse(include_bytes!("sample.json"))));
}

#[bench]
fn parze(b: &mut Bencher) {
    let json = parze::json();
    b.iter(|| black_box(json.parse(<&[_]>::from(include_bytes!("sample.json")))));
    //dbg!(parze::json().parse(<&[_]>::from(include_bytes!("sample.json"))));
}

mod pom {
    use pom::parser::*;
    use pom::Parser;

    use std::collections::HashMap;
    use std::str::{self, FromStr};
    use super::JsonValue;

    fn space() -> Parser<u8, ()> {
        one_of(b" \t\r\n").repeat(0..).discard()
    }

    fn number() -> Parser<u8, f64> {
        let integer = one_of(b"123456789") - one_of(b"0123456789").repeat(0..) | sym(b'0');
        let frac = sym(b'.') + one_of(b"0123456789").repeat(1..);
        let exp = one_of(b"eE") + one_of(b"+-").opt() + one_of(b"0123456789").repeat(1..);
        let number = sym(b'-').opt() + integer + frac.opt() + exp.opt();
        number.collect().convert(str::from_utf8).convert(|s|f64::from_str(&s))
    }

    fn string() -> Parser<u8, String> {
        let special_char = sym(b'\\') | sym(b'/') | sym(b'"')
            | sym(b'b').map(|_|b'\x08') | sym(b'f').map(|_|b'\x0C')
            | sym(b'n').map(|_|b'\n') | sym(b'r').map(|_|b'\r') | sym(b't').map(|_|b'\t');
        let escape_sequence = sym(b'\\') * special_char;
        let string = sym(b'"') * (none_of(b"\\\"") | escape_sequence).repeat(0..) - sym(b'"');
        string.convert(String::from_utf8)
    }

    fn array() -> Parser<u8, Vec<JsonValue>> {
        let elems = list(call(value), sym(b',') * space());
        sym(b'[') * space() * elems - sym(b']')
    }

    fn object() -> Parser<u8, HashMap<String, JsonValue>> {
        let member = string() - space() - sym(b':') - space() + call(value);
        let members = list(member, sym(b',') * space());
        let obj = sym(b'{') * space() * members - sym(b'}');
        obj.map(|members|members.into_iter().collect::<HashMap<_,_>>())
    }

    fn value() -> Parser<u8, JsonValue> {
        ( seq(b"null").map(|_|JsonValue::Null)
        | seq(b"true").map(|_|JsonValue::Bool(true))
        | seq(b"false").map(|_|JsonValue::Bool(false))
        | number().map(|num|JsonValue::Num(num))
        | string().map(|text|JsonValue::Str(text))
        | array().map(|arr|JsonValue::Array(arr))
        | object().map(|obj|JsonValue::Object(obj))
        ) - space()
    }

    pub fn json() -> Parser<u8, JsonValue> {
        space() * value() - end()
    }
}

mod parze {
    use parze::prelude::*;

    use std::str;
    use super::JsonValue;

    pub fn json() -> Parser<'static, u8, JsonValue> {
        recursive(|value| {
            let integer = one_of(b"123456789").chained()
                .chain(one_of(b"0123456789").repeat(..))
                .or_chain(sym(b'0').chained());
            let frac = sym(b'.').chained()
                .chain(one_of(b"0123456789").repeat(1..));
            let exp = one_of(b"eE").chained()
                .chain(one_of(b"+-").or_not())
                .chain(one_of(b"0123456789").repeat(1..));
            let number = sym(b'-').or_not()
                .chain(integer)
                .chain(frac.or_not().flatten())
                .chain(exp.or_not().flatten())
                .map(|bs| str::from_utf8(&bs.as_slice()).unwrap().parse().unwrap());

            let special_char = sym(b'\\')
                .or(sym(b'/'))
                .or(sym(b'"'))
                .or(sym(b'b').to(b'\x08'))
                .or(sym(b'f').to(b'\x0C'))
                .or(sym(b'n').to(b'\n'))
                .or(sym(b'r').to(b'\r'))
                .or(sym(b't').to(b'\t'));
            let escape_seq = sym(b'\\').delimiter_for(special_char);
            let string = sym(b'"')
                .delimiter_for(none_of(b"\\\"").or(escape_seq).repeat(0..))
                .delimited_by(sym(b'"'))
                .map(|bs| String::from_utf8(bs).unwrap());

            let elements = value.link().separated_by(sym(b',').padded());
            let array = sym(b'[').padded()
                .delimiter_for(elements)
                .delimited_by(sym(b']'));

            let member = string.clone().padded()
                .delimited_by(sym(b':').padded())
                .then(value.link());
            let members = member.separated_by(sym(b',').padded());
            let object = sym(b'{').padded()
                .delimiter_for(members)
                .delimited_by(sym(b'}'))
                .collect();

            padding().delimiter_for(
                    all_of(b"null").map(|_| JsonValue::Null)
                .or(all_of(b"true").map(|_| JsonValue::Bool(true)))
                .or(all_of(b"false").map(|_| JsonValue::Bool(false)))
                .or(number.map(|n| JsonValue::Num(n)))
                .or(string.map(|s| JsonValue::Str(s)))
                .or(array.map(|a| JsonValue::Array(a)))
                .or(object.map(|o| JsonValue::Object(o)))
            ).padded()
        })
    }
}
