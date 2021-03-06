#![cfg(feature = "macros")]
#![feature(proc_macro_hygiene)]
#![recursion_limit="256"]
#![type_length_limit="100000000"]

use parze::prelude::*;

fn main() {
    parsers!{
        morse: Parser<_, _> = {
            (
                ( { all_of(b"-...") } -> 'B'
                | { all_of(b"-.-.") } -> 'C'
                | { all_of(b"..-.") } -> 'F'
                | { all_of(b"....") } -> 'H'
                | { all_of(b".---") } -> 'J'
                | { all_of(b".-..") } -> 'L'
                | { all_of(b".--.") } -> 'P'
                | { all_of(b"--.-") } -> 'Q'
                | { all_of(b"...-") } -> 'V'
                | { all_of(b"-..-") } -> 'X'
                | { all_of(b"-.--") } -> 'Y'
                | { all_of(b"--..") } -> 'Z'
                | { all_of(b"-..") }  -> 'D'
                | { all_of(b"--.") }  -> 'G'
                | { all_of(b"-.-") }  -> 'K'
                | { all_of(b"---") }  -> 'O'
                | { all_of(b".-.") }  -> 'R'
                | { all_of(b"...") }  -> 'S'
                | { all_of(b"..-") }  -> 'U'
                | { all_of(b".--") }  -> 'W'
                | { all_of(b".-") }   -> 'A'
                | { all_of(b"..") }   -> 'I'
                | { all_of(b"--") }   -> 'M'
                | { all_of(b"-.") }   -> 'N'
                | { all_of(b".") }    -> 'E'
                | { all_of(b"-") }    -> 'T'
                )~
            ) * => { |cs| cs.collect::<String>() }
        }
    }

    println!("{}", morse.parse(b".... . .-.. .-.. --- .-- . .-.. -.-. --- -- . - --- .--. .- .-. --.. .").unwrap());
}
