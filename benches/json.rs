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
fn parze(b: &mut Bencher) {
    let json = parze::json();
    b.iter(|| black_box(json.parse(<&[_]>::from(include_bytes!("sample.json"))).unwrap()));
    //dbg!(parze::json().parse(<&[_]>::from(include_bytes!("small_sample.json"))));
}

#[bench]
fn pom(b: &mut Bencher) {
    let json = pom::json();
    b.iter(|| black_box(json.parse(include_bytes!("sample.json")).unwrap()));
}

/*
#[bench]
fn nom(b: &mut Bencher) {
    //b.iter(|| black_box(nom::root(include_str!("sample.json")).unwrap()));
    dbg!(nom::root(include_str!("small_sample.json")).unwrap());
}
*/

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

/*
// TODO: Find a nom JSON parser that actually works
mod nom {
    extern crate nom;

    use nom::{
        branch::alt,
        bytes::complete::{escaped, tag, take_while},
        character::complete::{char, one_of, none_of},
        combinator::{map, opt, cut},
        error::{context, VerboseError},
        multi::separated_list,
        number::complete::double,
        sequence::{delimited, preceded, separated_pair, terminated},
        IResult,
    };
    use std::collections::HashMap;
    use std::str;
    use super::JsonValue;

    fn sp<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
      let chars = " \t\r\n";

      take_while(move |c| chars.contains(c))(i)
    }

    fn parse_str<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
      escaped(none_of("\"\\"), '\\', one_of("\"n\\"))(i)
    }

    fn boolean<'a>(input: &'a str) -> IResult<&'a str, bool, VerboseError<&'a str>> {
      alt((
          map(tag("false"), |_| false),
          map(tag("true"), |_| true)
      ))(input)
    }

    fn string<'a>(i: &'a str) -> IResult<&'a str, &'a str, VerboseError<&'a str>> {
      context("string",
        preceded(
          char('\"'),
          cut(terminated(
              parse_str,
              char('\"')
      ))))(i)
    }

    fn array<'a>(i: &'a str) -> IResult<&'a str, Vec<JsonValue>, VerboseError<&'a str>> {
      context(
        "array",
        preceded(char('['),
        cut(terminated(
          separated_list(preceded(sp, char(',')), value),
          preceded(sp, char(']'))))
      ))(i)
    }

    fn key_value<'a>(i: &'a str) -> IResult<&'a str, (&'a str, JsonValue), VerboseError<&'a str>> {
    separated_pair(preceded(sp, string), cut(preceded(sp, char(':'))), value)(i)
    }

    fn hash<'a>(i: &'a str) -> IResult<&'a str, HashMap<String, JsonValue>, VerboseError<&'a str>> {
      context(
        "map",
        preceded(char('{'),
        cut(terminated(
          map(
            separated_list(preceded(sp, char(',')), key_value),
            |tuple_vec| {
              tuple_vec.into_iter().map(|(k, v)| (String::from(k), v)).collect()
          }),
          preceded(sp, char('}')),
        ))
      ))(i)
    }

    pub fn value<'a>(i: &'a str) -> IResult<&'a str, JsonValue, VerboseError<&'a str>> {
      preceded(
        sp,
        alt((
          map(hash, JsonValue::Object),
          map(array, JsonValue::Array),
          map(string, |s| JsonValue::Str(String::from(s))),
          map(double, JsonValue::Num),
          map(boolean, JsonValue::Bool),
        )),
      )(i)
    }

    pub fn root<'a>(i: &'a str) -> IResult<&'a str, JsonValue, VerboseError<&'a str>> {
      delimited(
        sp,
        alt((map(hash, JsonValue::Object), map(array, JsonValue::Array))),
        opt(sp),
      )(i)
    }
}
*/
