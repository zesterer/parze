use parze::prelude::*;

fn main() {
    // Define a parser for morse code
    let morse: Parser<_, _> = (
        (
              sym('-') + sym('.') + sym('.') + sym('.') - 'B'
            | sym('-') + sym('.') + sym('-') + sym('.') - 'C'
            | sym('.') + sym('.') + sym('-') + sym('.') - 'F'
            | sym('.') + sym('.') + sym('.') + sym('.') - 'H'
            | sym('.') + sym('-') + sym('-') + sym('-') - 'J'
            | sym('.') + sym('-') + sym('.') + sym('.') - 'L'
            | sym('.') + sym('-') + sym('-') + sym('.') - 'P'
            | sym('-') + sym('-') + sym('.') + sym('-') - 'Q'
            | sym('.') + sym('.') + sym('.') + sym('-') - 'V'
            | sym('-') + sym('.') + sym('.') + sym('-') - 'X'
            | sym('-') + sym('.') + sym('-') + sym('-') - 'Y'
            | sym('-') + sym('-') + sym('.') + sym('.') - 'Z'
            | sym('-') + sym('.') + sym('.')            - 'D'
            | sym('-') + sym('-') + sym('.')            - 'G'
            | sym('-') + sym('.') + sym('-')            - 'K'
            | sym('-') + sym('-') + sym('-')            - 'O'
            | sym('.') + sym('-') + sym('.')            - 'R'
            | sym('.') + sym('.') + sym('.')            - 'S'
            | sym('.') + sym('.') + sym('-')            - 'U'
            | sym('.') + sym('-') + sym('-')            - 'W'
            | sym('.') + sym('-')                       - 'A'
            | sym('.') + sym('.')                       - 'I'
            | sym('-') + sym('-')                       - 'M'
            | sym('-') + sym('.')                       - 'N'
            | sym('.')                                  - 'E'
            | sym('-')                                  - 'T'
        ) << sym(' ') * Any
    ) * Any % |cs| cs.into_iter().collect::<String>();

    println!("{}", morse.parse(".... . .-.. .-.. --- .-- . .-.. -.-. --- -- . - --- .--. .- .-. --.. .".chars().collect::<Vec<_>>()).unwrap());
}
