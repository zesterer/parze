#![cfg(feature = "macros")]
#![feature(proc_macro_hygiene)]

use parze::prelude::*;
use std::collections::HashMap;

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
        integer = { { one_of("123456789".chars()) }.% % { one_of("0123456789".chars()) }* |% '0'.% }
        frac = { '.'.% % { one_of("0123456789".chars()) }+ }
        exp = { ('e' | 'E').% % ('+' | '-')? % { one_of("0123456789".chars()) }+ }
        number = { '-'? % integer % frac?.# % exp?.# => { |cs| cs.collect::<String>().parse().unwrap() } }

        special = { '\\' | '/' | '"' | 'b' -> '\x08' | 'f' -> '\x0C' | 'n' -> '\n' | 'r' -> '\r' | 't' -> '\t' }
        escape = { '\\' -& special }
        string = { '"' -& ({ none_of("\\\"".chars()) } | escape)* &- '"' => { |cs| cs.collect::<String>() } }

        elements = { value ... ','~ }
        array = { '['~ -& elements &- ']' }

        member = { string~ &- ':'~ & value }
        members = { member ... ','~ }

        object = { '{'~ -& members &- '}' => { |m| m.collect() } }

        value: Parser<_, _> = {
            ~(
                | { all_of("null".chars()) } => { |_| JsonValue::Null }
                | { all_of("true".chars()) } => { |_| JsonValue::Bool(true) }
                | { all_of("false".chars()) } => { |_| JsonValue::Bool(false) }
                | number => { |n| JsonValue::Num(n) }
                | string => { |s| JsonValue::Str(s) }
                | array => { |a| JsonValue::Array(a) }
                | object => { |o| JsonValue::Object(o) }
            )~
        }
    }

    let test_json = r#"
        {
            "parze": {
                "description": "parser combinator library",
                "has_macros": true
            },
            "some_numbers": [42, 13.37, 256],
            "hypothesis": null
        }
    "#;

    println!("{:#?}", value.parse_str(test_json));
}
