use parze::prelude::*;

fn main() {
    // Define a parser for morse code
    let morse: Parser<_, _> = (
        (
              all_of(b"-...") - 'B'
            | all_of(b"-.-.") - 'C'
            | all_of(b"..-.") - 'F'
            | all_of(b"....") - 'H'
            | all_of(b".---") - 'J'
            | all_of(b".-..") - 'L'
            | all_of(b".--.") - 'P'
            | all_of(b"--.-") - 'Q'
            | all_of(b"...-") - 'V'
            | all_of(b"-..-") - 'X'
            | all_of(b"-.--") - 'Y'
            | all_of(b"--..") - 'Z'
            | all_of(b"-..")  - 'D'
            | all_of(b"--.")  - 'G'
            | all_of(b"-.-")  - 'K'
            | all_of(b"---")  - 'O'
            | all_of(b".-.")  - 'R'
            | all_of(b"...")  - 'S'
            | all_of(b"..-")  - 'U'
            | all_of(b".--")  - 'W'
            | all_of(b".-")   - 'A'
            | all_of(b"..")   - 'I'
            | all_of(b"--")   - 'M'
            | all_of(b"-.")   - 'N'
            | all_of(b".")    - 'E'
            | all_of(b"-")    - 'T'
        ).padded_by(b' ')
    ) * Any % |cs| cs.into_iter().collect::<String>();

    println!("{}", morse.parse(<&[_]>::from(b".... . .-.. .-.. --- .-- . .-.. -.-. --- -- . - --- .--. .- .-. --.. .")).unwrap());
}
