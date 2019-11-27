pub trait Padded {
    fn is_padding(&self) -> bool;
}

impl Padded for char {
    fn is_padding(&self) -> bool {
        self.is_whitespace()
    }
}

impl Padded for u8 {
    fn is_padding(&self) -> bool {
        self.is_ascii_whitespace()
    }
}
