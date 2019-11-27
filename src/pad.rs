/// A trait to interpret symbols as padding.
///
/// Implement this trait for your own types to allow padding-related functionality
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
