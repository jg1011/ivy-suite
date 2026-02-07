//! Five-Hand evaluation logic

use crate::card::{Card, CardParseError};
use crate::generated::{FIVE_FLUSH_HASH, FIVE_NONFLUSH_HASH};
use std::fmt;
use std::str::FromStr;
use thiserror::Error;

#[derive(Clone, Copy)]
#[repr(transparent)] // enforce layout = [Card; 5] = [u32; 5]
pub struct FiveHand([Card; 5]);

impl FiveHand {
    /// Zero cost downcast into [Card; 5] array
    pub fn as_card_array(&self) -> [Card; 5] {
        self.0 // zero cost abstraction
    }

    /// Zero cost downcast into [u32; 5]
    pub fn as_u32_array(self) -> [u32; 5] {
        unsafe {
            // safety ensured by transparent repr; zero runtime cost
            std::mem::transmute(self)
        }
    }

    /// Determines hand rank from codegen hashes
    pub fn rank(&self) -> u32 {
        let hand = self.as_u32_array();
        let mut p = 1;
        for card in hand {
            p *= card & 0b111_111
        }
        match is_flush(&hand) {
            true => *FIVE_FLUSH_HASH.get(&p).unwrap(),
            false => *FIVE_NONFLUSH_HASH.get(&p).unwrap(),
        }
    }
}

/// Determines whether hand is a flush
///
/// Computed via noting
///     flush <==> c1 & c2 & c3 & c4 & c5 & (0b1111 << 12)
/// where c_i is card i as u32 w/ xxxb:bbbb|bbbb:bbbb|ssss:rrrr|xxpp:pppp repr
fn is_flush(&hand: &[u32; 5]) -> bool {
    let bit_mask: u32 = 0b1111 << 12; // 1's at ssss in u32 Card repr
    !((hand[0] & hand[1] & hand[2] & hand[3] & hand[4] & bit_mask) == 0b0000)
}

// -- parsing -- // 

#[derive(Error, Debug, PartialEq)]
pub enum FiveHandParseError {
    #[error("Card Error")]
    InvalidCard(#[from] CardParseError),

    #[error(r#"Invalid Number of cards, expected five cards: got {0} \n 
            valid delimiters = {{" ", "-", "_", ",", ";"}} "#)]
    InvalidNumCards(usize)
}

impl FromStr for FiveHand {
    type Err = FiveHandParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let delims = [' ', '-', '_', ',', ';'];
        let card_strs = s.split(|c| delims.contains(&c)).filter(|s| !s.is_empty()).collect::<Vec<&str>>(); 

        if card_strs.len() != 5 {
            return Err(FiveHandParseError::InvalidNumCards(card_strs.len()))
        }

        let mut it = card_strs.into_iter();

        // len==5 established; unwrap safe
        let card_arr: [Card; 5] = [
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
        ];

        Ok(FiveHand(card_arr))
    }
}


// -- displaying -- // 

impl fmt::Display for FiveHand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cards = self.as_card_array();
        write!(f, "{} {} {} {} {}", cards[0], cards[1], cards[2], cards[3], cards[4])
    }
}

impl fmt::Debug for FiveHand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let raw = self.as_u32_array();
        write!(f, "FiveHand([")?;
        for (i, val) in raw.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{:#010x}", val)?;
        }
        write!(f, "])")
    }
}

// -- testing -- // 

#[cfg(test)]
mod tests {
    use super::*;
    use crate::card::{Rank, Suit};

    #[test]
    fn test_five_hand_parse_accuracy() {
        let hand_str = "Ah Kh Qh Jh Th";
        let hand = FiveHand::from_str(hand_str).expect("Royal Flush Invalid: God is dead");
        let cards = hand.as_card_array();

        assert_eq!(cards[0], Card::new(Rank::Ace, Suit::Hearts));
        assert_eq!(cards[1], Card::new(Rank::King, Suit::Hearts));
        assert_eq!(cards[2], Card::new(Rank::Queen, Suit::Hearts));
        assert_eq!(cards[3], Card::new(Rank::Jack, Suit::Hearts));
        assert_eq!(cards[4], Card::new(Rank::Ten, Suit::Hearts));
    }

    #[test]
    fn test_five_hand_delimiters() {
        let variations = [
            "2h-3d-4s-5c-6h",
            "2h_3d_4s_5c_6h",
            "2h,3d,4s,5c,6h",
            "2h;3d;4s;5c;6h",
            "6d 3d 2d As 9c",
            "2h  3d , 4s;5c___6h", 
        ];

        for s in variations {
            assert!(
                FiveHand::from_str(s).is_ok(),
                "Failed to parse valid hand with delimiters: {}",
                s
            );
        }
    }

    #[test]
    fn test_five_hand_parse_invalid_count() {
        let short = "Ah Kd Qs Js";
        let res_short = FiveHand::from_str(short);
        assert!(matches!(
            res_short,
            Err(FiveHandParseError::InvalidNumCards(4))
        ));

        let long = "Ah Kd Qs Js Tc 9h";
        let res_long = FiveHand::from_str(long);
        assert!(matches!(
            res_long,
            Err(FiveHandParseError::InvalidNumCards(6))
        ));
    }

    #[test]
    fn test_five_hand_parse_invalid_card_error_propagation() {
        let input = "Ah Kd Qx Js Tc"; // 'Qx' invalid suit
        let res = FiveHand::from_str(input);

        match res {
            Err(FiveHandParseError::InvalidCard(CardParseError::InvalidSuit(s))) => {
                assert_eq!(s, "x");
            }
            _ => panic!("Expected InvalidCard(InvalidSuit), got {:?}", res),
        }
    }
}