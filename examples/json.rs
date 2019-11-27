#![cfg(feature = "macros")]
#![feature(proc_macro_hygiene)]

use parze::prelude::*;
use std::{collections::HashMap, str};

#[derive(Debug, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Str(String),
    Num(f64),
    Array(Vec<JsonValue>),
    Object(HashMap<String,JsonValue>)
}

fn main() {
    parsers! {
        integer = { { one_of(b"123456789") }.% % { one_of(b"0123456789") }* |% b'0'.% }
        frac = { b'.'.% % { one_of(b"0123456789") }+ }
        exp = { (b'e' | b'E').% % (b'+' | b'-')? % { one_of(b"0123456789") }+ }
        number = { b'-'? % integer % frac?.# % exp?.# => { |b| str::from_utf8(&b.as_slice()).unwrap().parse().unwrap() } }

        special = { b'\\' | b'/' | b'"' | b'b' -> b'\x08' | b'f' -> b'\x0C' | b'n' -> b'\n' | b'r' -> b'\r' | b't' -> b'\t' }
        escape = { b'\\' -& special }
        string = { b'"' -& ({ none_of(b"\\\"") } | escape)* &- b'"' => { |b| String::from_utf8(b).unwrap() } }

        elements = { value ... b','~ }
        array = { b'['~ -& elements &- b']' }

        member = { string~ &- b':'~ & value }
        members = { member ... b','~ }

        object = { b'{'~ -& members &- b'}' => { |m| m.into_iter().collect() } }

        value: Parser<_, _> = {
            ~(
                | { all_of(b"null") } => { |_| JsonValue::Null }
                | { all_of(b"true") } => { |_| JsonValue::Bool(true) }
                | { all_of(b"false") } => { |_| JsonValue::Bool(false) }
                | number => { |n| JsonValue::Num(n) }
                | string => { |s| JsonValue::Str(s) }
                | array => { |a| JsonValue::Array(a) }
                | object => { |o| JsonValue::Object(o) }
            )~
        }
    }

    let test_json = br#"
        {
            "parze": {
                "description": "parser combinator library",
                "has_macros": true
            },
            "some_numbers": [42, 13.37, 256],
            "hypothesis": null
        }
    "#;

    println!("{:#?}", value.parse(<&[_]>::from(test_json)));
}
