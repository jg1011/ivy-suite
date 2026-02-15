pub mod card;
pub mod five;
mod seven;

mod generated {
    include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
}

pub use card::{Card, Rank, Suit};
pub use five::FiveHand;
pub use seven::SevenHand;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assert_hash_lengths() {
        // lengths via doing the combinatorics by hand; see build.rs consts for details
        // use http://suffe.cool/poker/7462.html if you cant count ;)
        assert_eq!(generated::FIVE_FLUSH_HASH.len(), 1287);
        assert_eq!(generated::FIVE_NONFLUSH_HASH.len(), 6175);
    }
}
