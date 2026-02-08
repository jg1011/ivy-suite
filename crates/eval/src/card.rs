//! Card-level logic

use std::fmt;
use std::str::FromStr;
use thiserror::Error;

const PRIMES: [u32; 13] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];

/// Convenience enum: human readable suits as byte
#[repr(u8)]
pub enum Suit {
    Hearts = 0,
    Diamonds = 1,
    Spades = 2,
    Clubs = 3,
}

/// Convenience enum: human readable card rank as byte
#[repr(u8)]
pub enum Rank {
    Two = 0,
    Three = 1,
    Four = 2,
    Five = 3,
    Six = 4,
    Seven = 5,
    Eight = 6,
    Nine = 7,
    Ten = 8,
    Jack = 9,
    Queen = 10,
    King = 11,
    Ace = 12,
}

/// u32 typecast of Card:
///     xxxb:bbbb|bbbb:bbbb|ssss:rrrr|xxpp:pppp
/// where
///     x's are unused bits
///     b's are rank bitflags (A=0x1000... ; K=0x0100... etc)
///     s's are suit bitflags (H=0x0001 ; D=0x0010 ; S=0x0100 ; C=0x1000)
///     r's give rank nibble (0x0000-0x1100 <-> 2-A)
///     p's are prime rank repr bits (two=2, three=3, four=5, ... , ace=41)
#[derive(Clone, PartialEq, Eq, Copy)]
pub struct Card(u32);

impl Card {
    pub fn new(rank: Rank, suit: Suit) -> Self {
        // integer recastings
        let r = rank as u32;
        let s = suit as u32;
        let p: u32 = PRIMES[r as usize];
        // bit recastings && shift to xxxb:bbbb|bbbb:bbbb|ssss:rrrr|xxpp:pppp
        let r_bits = r << 8; // 0 <= r <= 12 < 15 ; safe cast to u4
        let s_bitflag: u32 = (1 << s) << 12; // one hot: 1 << s gives 1 in pos s  
        let r_bitflag: u32 = (1 << r) << 16; // one hot: same trick as w/ s_bitflag
        Card(p + r_bits + s_bitflag + r_bitflag)
    }

    /// downcast to u32
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    pub fn rank(&self) -> Rank {
        let r = (&self.as_u32() >> 8) & 0b1111; // mask onto rank nibble
        unsafe {
            // safety ensured by u8 repr of rank
            std::mem::transmute(r as u8)
        }
    }

    pub fn suit(&self) -> Suit {
        let s_one_hot = (&self.as_u32() >> 12) & 0b1111; // mask onto suit nibble
        let s = s_one_hot.trailing_zeros(); // 1 instr; trailing(0100) = 2 = spades etc
        unsafe {
            // safety ensured by u8 repr of rank
            std::mem::transmute(s as u8)
        }
    }
}

// -- parsing -- //

#[derive(Error, Debug, PartialEq)]
pub enum CardParseError {
    #[error("Invalid string length: expected 2 chars (e.g., 'Ah'), got {0}")]
    InvalidLength(usize),

    #[error("Unknown rank: {0}")]
    InvalidRank(String),

    #[error("Unknown suit: {0}")]
    InvalidSuit(String),
}

impl FromStr for Rank {
    type Err = CardParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "2" => Ok(Rank::Two),
            "3" => Ok(Rank::Three),
            "4" => Ok(Rank::Four),
            "5" => Ok(Rank::Five),
            "6" => Ok(Rank::Six),
            "7" => Ok(Rank::Seven),
            "8" => Ok(Rank::Eight),
            "9" => Ok(Rank::Nine),
            "T" => Ok(Rank::Ten),
            "J" => Ok(Rank::Jack),
            "Q" => Ok(Rank::Queen),
            "K" => Ok(Rank::King),
            "A" => Ok(Rank::Ace),
            _ => Err(CardParseError::InvalidRank(s.to_string())),
        }
    }
}

impl FromStr for Suit {
    type Err = CardParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_uppercase().as_str() {
            "H" => Ok(Suit::Hearts),
            "D" => Ok(Suit::Diamonds),
            "S" => Ok(Suit::Spades),
            "C" => Ok(Suit::Clubs),
            _ => Err(CardParseError::InvalidSuit(s.to_string())),
        }
    }
}

impl FromStr for Card {
    type Err = CardParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Standard format is 2 chars: "Ah", "Td", "2s"
        if s.chars().count() != 2 {
            return Err(CardParseError::InvalidLength(s.len()));
        }

        let mut chars = s.chars();
        let rank_char = chars.next().unwrap(); // unwrap safe due to count check
        let suit_char = chars.next().unwrap(); // unwrap safe due to count check

        let rank = rank_char.to_string().parse::<Rank>()?;
        let suit = suit_char.to_string().parse::<Suit>()?;

        Ok(Card::new(rank, suit))
    }
}

// -- displaying -- //

impl fmt::Display for Rank {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = match self {
            Rank::Two => '2',
            Rank::Three => '3',
            Rank::Four => '4',
            Rank::Five => '5',
            Rank::Six => '6',
            Rank::Seven => '7',
            Rank::Eight => '8',
            Rank::Nine => '9',
            Rank::Ten => 'T',
            Rank::Jack => 'J',
            Rank::Queen => 'Q',
            Rank::King => 'K',
            Rank::Ace => 'A',
        };
        write!(f, "{}", c)
    }
}

impl fmt::Display for Suit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = match self {
            Suit::Hearts => 'h',
            Suit::Diamonds => 'd',
            Suit::Spades => 's',
            Suit::Clubs => 'c',
        };
        write!(f, "{}", c)
    }
}

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.rank(), self.suit())
    }
}

impl fmt::Debug for Card {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Card({} [{:#034b}])", self, self.0)
    }
}

// -- tests -- //

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_card_parse_successes() {
        assert!("Th".parse::<Card>().is_ok());
        assert!("As".parse::<Card>().is_ok()); // rip lemmy
        assert!("4d".parse::<Card>().is_ok());
        assert!("7c".parse::<Card>().is_ok());

        // manually check bytes for Jh
        let jh_prime_repr = PRIMES[9];
        let jh_rank_nibble = (9_u32 << 8) as u32;
        let jh_suit_one_hot = (0b0001 << 12) as u32; // see Card docstring for one-hot schema
        let jh_rank_one_hot = (0b0_0010_0000_0000 << 16) as u32;
        let jh_raw = Card(jh_prime_repr + jh_rank_nibble + jh_suit_one_hot + jh_rank_one_hot);

        let jh_parsed = "Jh".parse::<Card>().unwrap();
        assert_eq!(jh_raw, jh_parsed);
    }

    #[test]
    fn test_card_parse_failures() {
        assert!(matches!(
            "10h".parse::<Card>(),
            Err(CardParseError::InvalidLength(3))
        )); // use "Th" to get expected behaviour
        assert!(matches!(
            "Xh".parse::<Card>(),
            Err(CardParseError::InvalidRank(_))
        ));
        assert!(matches!(
            "Az".parse::<Card>(),
            Err(CardParseError::InvalidSuit(_))
        ));
    }
}
