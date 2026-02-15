#![allow(unused)]

use crate::card::{Card, CardParseError};
use crate::five::FiveHand;
use std::fmt;
use std::str::FromStr;
use thiserror::Error;

#[cfg(test)]
fn debug_trace() -> bool {
    std::env::var("DEBUG_BEST_FIVE_BRANCHLESS").is_ok()
}

/// utility macro: standard carry_save addition of 3 n-bit numbers; returns tuple with items
///
/// - partial_sum = a XOR b XOR c
/// - shift_carry = (a AND b) OR (a AND c) OR (b AND C) = (a AND b) OR (c AND (a XOR b))
///
/// respectively. All operations are bitwise
///
/// note: shift_carry is simply the bitwise majority fn; returns 1 iff at least two of a, b, c
///
/// ref: https://en.wikipedia.org/wiki/Carry-save_adder#Technical_details
/// additional ref: http://www.quadibloc.com/comp/cp0202.htm (more esoteric but cooler)
///
/// shoutout John von Neumann
macro_rules! carry_save_adder {
    ($a:expr, $b:expr, $c:expr) => {{
        let partial_sum = $a ^ $b ^ $c;
        let shift_carry = ($a & $b) | ($c & ($a ^ $b));
        (partial_sum, shift_carry)
    }};
}

#[derive(Clone, Copy)]
#[repr(transparent)] // enforce layout = [Card; 7] = [u32; 7]
pub struct SevenHand([Card; 7]);

impl SevenHand {
    pub fn from_card_array(cards: [Card; 7]) -> Self {
        Self(cards)
    }

    pub fn as_card_array(&self) -> [Card; 7] {
        self.0
    }

    pub fn as_u32_array(self) -> [u32; 7] {
        unsafe {
            // safety ensured by transparent repr; zero runtime cost
            std::mem::transmute(self)
        }
    }

    /// DIVINE zero branching highest rank five-card hand selector
    pub fn best_five_branchless(&self) -> FiveHand {
        let card_arr = self.as_u32_array(); 

        #[cfg(test)]
        if debug_trace() {
            eprintln!(
                "[best_five] input cards: [0x{:08x}, 0x{:08x}, 0x{:08x}, 0x{:08x}, 0x{:08x}, 0x{:08x}, 0x{:08x}]",
                card_arr[0],
                card_arr[1],
                card_arr[2],
                card_arr[3],
                card_arr[4],
                card_arr[5],
                card_arr[6]
            );
            eprintln!("[best_five] input hand: {}", self);
        }

        let ((_p1, p2, p3), (c1_s, c2_s, c3_s)) = find_recurrer_unions_branchless(&card_arr);
        let flush_union = find_flush_union_branchless(&card_arr);
        let r_seed_ext = find_straight_seed_branchless(&card_arr);
        let top_straight_cards = find_top_straight_cards_branchless(&card_arr, r_seed_ext);

        #[cfg(test)]
        if debug_trace() {
            eprintln!(
                "[best_five] r_seed_ext=0x{:04x} flush_union=0x{:08x} top_straight_cards=[0x{:08x},0x{:08x},0x{:08x},0x{:08x},0x{:08x}]",
                r_seed_ext,
                flush_union,
                top_straight_cards[0],
                top_straight_cards[1],
                top_straight_cards[2],
                top_straight_cards[3],
                top_straight_cards[4]
            );
        }

        let f_ranks = (flush_union >> 16) & 0x1FFF;
        let f_seed = f_ranks & (f_ranks >> 1) & (f_ranks >> 2) & (f_ranks >> 3) & (f_ranks >> 4);
        let is_sf = ((f_seed != 0) as u32).wrapping_neg();

        let is_quads = ((c3_s == 4) as u32).wrapping_neg();
        let is_fh = (((c3_s == 3) & (c2_s >= 2)) as u32).wrapping_neg();
        let is_flush = ((flush_union.count_ones() >= 5) as u32).wrapping_neg();
        let is_str = ((r_seed_ext != 0) as u32).wrapping_neg(); // r_seed_ext is 0 if no straight
        let is_trips = ((c3_s == 3) as u32).wrapping_neg();
        let is_2p = (((c3_s == 2) & (c2_s == 2)) as u32).wrapping_neg();
        let is_pair = ((c3_s == 2) as u32).wrapping_neg();

        // P-MUX w/ priority system:
        // bit 31 = primary filter (e.g. trips in full house, higher pair in two-pair)
        // bit 30 = secondary filter (e.g. pair in full house, lower pair in two-pair)

        // dflt = no mask
        let mut mask_prim = 0u32;
        let mut mask_sec = 0u32;

        //  Hierarchy Logic: val = (new & mask) | (old & !mask)

        mask_prim = (p3 & is_pair) | (mask_prim & !is_pair);

        mask_prim = (p3 & is_2p) | (mask_prim & !is_2p);
        mask_sec = (p2 & is_2p) | (mask_sec & !is_2p);

        mask_prim = (p3 & is_trips) | (mask_prim & !is_trips);
        mask_sec = (0 & is_trips) | (mask_sec & !is_trips); // Clear secondary

        // Straight uses exact-match (top_straight_cards), not mask - clear mask_prim for straight
        mask_prim = (0u32 & is_str) | (mask_prim & !is_str);

        #[cfg(test)]
        if debug_trace() {
            eprintln!(
                "[best_five] after straight step: is_str=0x{:08x} (straight uses exact-match, not mask)",
                is_str
            );
        }

        mask_prim = (flush_union & is_flush) | (mask_prim & !is_flush);

        mask_prim = (p3 & is_fh) | (mask_prim & !is_fh);
        mask_sec = (p2 & is_fh) | (mask_sec & !is_fh);

        mask_prim = (p3 & is_quads) | (mask_prim & !is_quads);
        mask_sec = (0 & is_quads) | (mask_sec & !is_quads);

        // reconstruct straight flush card union: cards that are BOTH flush-suit AND SF-rank.
        // flush_union & f_cover only keeps rank bitflags (bits 16+), losing suit/prime/nibble bits,
        // which breaks the (c & mask) == c subset test. Instead, accumulate the actual card union.
        // definitely wasted some cycles here...
        let f_cover =
            (f_seed | (f_seed << 1) | (f_seed << 2) | (f_seed << 3) | (f_seed << 4)) << 16;
        let flush_suit = flush_union & 0xF000; // suit one-hot from flush union

        let mut sf_card_union = 0u32;
        for i in 0..7 {
            let c = card_arr[i];
            let in_suit = ((c & flush_suit) != 0) as u32;
            let in_rank = ((c & f_cover) != 0) as u32;
            let hit = (in_suit & in_rank).wrapping_neg();
            sf_card_union |= c & hit;
        }

        // SF primary = SF cards; SF secondary = irrelevant (all SF cards are primary)
        mask_prim = (sf_card_union & is_sf) | (mask_prim & !is_sf);
        mask_sec = (0 & is_sf) | (mask_sec & !is_sf);

        #[cfg(test)]
        if debug_trace() {
            eprintln!(
                "[best_five] c1_s={} c2_s={} c3_s={} is_str=0x{:08x} is_flush=0x{:08x} mask_prim=0x{:08x} mask_sec=0x{:08x}",
                c1_s, c2_s, c3_s, is_str, is_flush, mask_prim, mask_sec
            );
        }

        let mut keys = [0u32; 7];

        for i in 0..7 {
            let c = card_arr[i];

            // Plain straight: exact-match (one per rank). SF/other: subset match via mask.
            // SF cards are same suit => no duplicate-rank issue => mask path is correct for SF.
            let use_str_path = is_str & !is_sf;
            let is_p_str = ((c == top_straight_cards[0])
                || (c == top_straight_cards[1])
                || (c == top_straight_cards[2])
                || (c == top_straight_cards[3])
                || (c == top_straight_cards[4])) as u32;
            let is_p_mask = ((c & mask_prim) == c) as u32;
            let is_p = (is_p_str & use_str_path) | (is_p_mask & !use_str_path);

            let bit_p = is_p << 31;
            let is_s = ((c & mask_sec) == c) as u32;
            let bit_s = is_s << 30;

            keys[i] = c | bit_p | bit_s;

            #[cfg(test)]
            if debug_trace() {
                let card: Card = unsafe { std::mem::transmute(c.clone()) };
                eprintln!(
                    "[best_five] [card {}] {} (0x{:08x}) is_p={} key=0x{:08x}",
                    i, card, c, is_p, keys[i]
                );
            }
        }

        sort_network_7_desc(&mut keys);

        #[cfg(test)]
        if debug_trace() {
            let keys_cards: [Card; 7] = unsafe {
                std::mem::transmute([
                    keys[0] & 0x3FFFFFFF,
                    keys[1] & 0x3FFFFFFF,
                    keys[2] & 0x3FFFFFFF,
                    keys[3] & 0x3FFFFFFF,
                    keys[4] & 0x3FFFFFFF,
                    keys[5] & 0x3FFFFFFF,
                    keys[6] & 0x3FFFFFFF,
                ])
            };

            eprintln!(
                "[best_five] keys_after_sort: [{} {} {} {} {} {} {}]",
                keys_cards[0],
                keys_cards[1],
                keys_cards[2],
                keys_cards[3],
                keys_cards[4],
                keys_cards[5],
                keys_cards[6]
            );
        }

        // Straight: use top_straight_cards (sort can misorder one-per-rank). Else: use sorted keys.
        // Branchless mux: m = 0xFFFF_FFFF when straight, 0 otherwise.
        let m = is_str & !is_sf; // plain straight only; SF goes through sort path
        let straight5 = [
            top_straight_cards[0] & 0x3FFFFFFF,
            top_straight_cards[1] & 0x3FFFFFFF,
            top_straight_cards[2] & 0x3FFFFFFF,
            top_straight_cards[3] & 0x3FFFFFFF,
            top_straight_cards[4] & 0x3FFFFFFF,
        ];
        let sort5 = [
            keys[0] & 0x3FFFFFFF,
            keys[1] & 0x3FFFFFFF,
            keys[2] & 0x3FFFFFFF,
            keys[3] & 0x3FFFFFFF,
            keys[4] & 0x3FFFFFFF,
        ];
        let final_hand = [
            (straight5[0] & m) | (sort5[0] & !m),
            (straight5[1] & m) | (sort5[1] & !m),
            (straight5[2] & m) | (sort5[2] & !m),
            (straight5[3] & m) | (sort5[3] & !m),
            (straight5[4] & m) | (sort5[4] & !m),
        ];

        #[cfg(test)]
        if debug_trace() {
            let five: FiveHand = unsafe { std::mem::transmute(final_hand) };
            let final_cards: [Card; 5] = unsafe { std::mem::transmute(final_hand) };
            eprintln!(
                "[best_five] final_hand: [{} {} {} {} {}] rank={}",
                final_cards[0],
                final_cards[1],
                final_cards[2],
                final_cards[3],
                final_cards[4],
                five.rank()
            );
        }

        unsafe {
            // bismallah
            std::mem::transmute(final_hand)
        }
    }
}

// -- parsing -- //

#[derive(Error, Debug, PartialEq)]
pub enum SevenHandParseError {
    #[error("Card Error")]
    InvalidCard(#[from] CardParseError),

    #[error(
        r#"Invalid Number of cards, expected seven cards: got {0} \n 
            valid delimiters = {{" ", "-", "_", ",", ";"}} "#
    )]
    InvalidNumCards(usize),
}

impl FromStr for SevenHand {
    type Err = SevenHandParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let delims = [' ', '-', '_', ',', ';'];
        let card_strs = s
            .split(|c| delims.contains(&c))
            .filter(|s| !s.is_empty())
            .collect::<Vec<&str>>();

        if card_strs.len() != 7 {
            return Err(SevenHandParseError::InvalidNumCards(card_strs.len()));
        }

        let mut it = card_strs.into_iter();

        let card_arr: [Card; 7] = [
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
            Card::from_str(it.next().unwrap())?,
        ];

        Ok(SevenHand::from_card_array(card_arr))
    }
}

// -- displaying -- //

impl fmt::Display for SevenHand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cards = self.as_card_array();
        write!(
            f,
            "{} {} {} {} {} {} {}",
            cards[0], cards[1], cards[2], cards[3], cards[4], cards[5], cards[6]
        )
    }
}

impl fmt::Debug for SevenHand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let raw = self.as_u32_array();
        write!(f, "SevenHand([")?;
        for (i, val) in raw.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:#010x}", val)?;
        }
        write!(f, "])")
    }
}

// -- helpers -- //

/// 7-element sorting network (Descending); swaps in place
///
/// 16 comparators in 6 depth layers (optimal for N=7).
/// Ref: https://bertdobbelaere.github.io/sorting_networks.html#N7 (thanks Knuth!)
#[inline(always)]
fn sort_network_7_desc(a: &mut [u32; 7]) {
    /// Branchless Compare-and-Swap (descending): swap if a[j] > a[i]
    ///
    /// NOTE: using an if should compile down to a cmov, but we're having fun here cmon
    macro_rules! cas {
        ($i:expr, $j:expr) => {
            let gt = ((a[$j] > a[$i]) as u32).wrapping_neg(); // 0xFFFFFFFF if swap else 0
            let old_i = a[$i];
            a[$i] = (a[$j] & gt) | (a[$i] & !gt);
            a[$j] = (old_i & gt) | (a[$j] & !gt);
        };
    }

    // 16 comparators, 6 depth layers for N=7
    // Layer 1
    cas!(0, 6);
    cas!(2, 3);
    cas!(4, 5);
    // Layer 2
    cas!(0, 2);
    cas!(1, 4);
    cas!(3, 6);
    // Layer 3
    cas!(0, 1);
    cas!(2, 5);
    cas!(3, 4);
    // Layer 4
    cas!(1, 2);
    cas!(4, 6);
    // Layer 5
    cas!(2, 3);
    cas!(4, 5);
    // Layer 6
    cas!(1, 2);
    cas!(3, 4);
    cas!(5, 6);
}

/// finds multi-occurrences of ranks in u32-array SevenCard repr w/o branching
///
/// Returns ((p1, p2, p3), (c1_s, c2_s, c3_s)) where:
///     - p3 = primary group (highest count, then highest rank) — quads/trips/high pair
///     - p2 = secondary group — pair in FH, low pair in 2P
///     - p1 = tertiary (3rd pair)
///     - ci_s = count_ones of corresponding pi, i=1,2,3
///
/// Algorithm:
///     1. use 3-element carry-save addition to count rank occurrences
///     2. isolate rank one-hots for multi-occurers w/ two's comp- LSB extraction
///     3. accumulate the 3 card unions on "if rank = multi-occurer" predicate over cards w/ mask
///     4. branchless bubble sort by count DESC (stable on rank ASC)
#[inline(always)]
fn find_recurrer_unions_branchless(cards: &[u32; 7]) -> ((u32, u32, u32), (u32, u32, u32)) {
    let rank_mask = 0x1FFF << 16; // get "b" bits in Card bit repr (rank one-hots at bits 16-28) 

    #[cfg(test)]
    if debug_trace() {
        eprintln!("[find_recurrer] rank_mask=0x{:08x}", rank_mask);
    }

    // shameless register abuse (refactor to use get_unchecked?)
    let c1 = cards[0];
    let m1 = c1 & rank_mask;
    let c2 = cards[1];
    let m2 = c2 & rank_mask;
    let c3 = cards[2];
    let m3 = c3 & rank_mask;
    let c4 = cards[3];
    let m4 = c4 & rank_mask;
    let c5 = cards[4];
    let m5 = c5 & rank_mask;
    let c6 = cards[5];
    let m6 = c6 & rank_mask;
    let c7 = cards[6];
    let m7 = c7 & rank_mask;

    // pop count: bit i of bj = 2^j term in binary expansion of # occurs of rank i in cards arr
    let (s123, c123) = carry_save_adder!(m1, m2, m3);
    let (s456, c456) = carry_save_adder!(m4, m5, m6);
    let (b0, c_low) = carry_save_adder!(s123, s456, m7);
    let (b1, b2) = carry_save_adder!(c123, c456, c_low);

    let geq_2_ranks = (b1 | b2) & rank_mask; // rank multi-hot for >=2 occurers

    // isolate one-hots from geq_2: {A, B, C} -> {A}, {B}, {C} (A, B & C can be 0, so can one-hots)
    // `a & (0.wrapping_sub(a))` isolates LSB of a, proof below (common trick I forget lol):
    // -- 0.wrapping_sub(a) = -a (two's comp-) = NOT(a) + 1 => a AND (NOT(a) + 1) = one_hot
    // -- where last equality follows via carrying ones, then stopping carry :)
    // there is an experimental way, see https://github.com/rust-lang/rust/issues/136909
    let geq_2_1 = geq_2_ranks & (0u32.wrapping_sub(geq_2_ranks)); // {A}
    let rem1 = geq_2_ranks ^ geq_2_1; // {A, B, C} \ {A} = {B, C}
    let geq_2_2 = rem1 & (0u32.wrapping_sub(rem1)); // {B}
    let geq_2_3 = rem1 ^ geq_2_2; // {B, C} \ {B} = {C}

    // card union accumulators
    let mut u1 = 0_u32;
    let mut u2 = 0_u32;
    let mut u3 = 0_u32;

    /// bitwise union and assign to accumulators ui (i=1,2,3) card x if predicate_i where
    ///     - if rank(x) = one_hot_i {predicate_i = true} else {predicate_i = false}
    /// $x is card u32, $m:expr is card rank one-hot
    ///
    /// uses (for u32 `a`) `(a | - a) >> 31 = 0` iff `a = 0` else `(a | - a) >> 31 = 0xFFFF_FFFF` trick
    macro_rules! accumulate_if_found {
        ($x:expr, $m:expr) => {
            let predicate_mask_1 =
                (($m & geq_2_1 | (0u32.wrapping_sub($m & geq_2_1))) as i32 >> 31) as u32;
            let predicate_mask_2 =
                (($m & geq_2_2 | (0u32.wrapping_sub($m & geq_2_2))) as i32 >> 31) as u32;
            let predicate_mask_3 =
                (($m & geq_2_3 | (0u32.wrapping_sub($m & geq_2_3))) as i32 >> 31) as u32;
            u1 |= $x & predicate_mask_1;
            u2 |= $x & predicate_mask_2;
            u3 |= $x & predicate_mask_3;
        };
    }

    accumulate_if_found!(c1, m1);
    accumulate_if_found!(c2, m2);
    accumulate_if_found!(c3, m3);
    accumulate_if_found!(c4, m4);
    accumulate_if_found!(c5, m5);
    accumulate_if_found!(c6, m6);
    accumulate_if_found!(c7, m7);

    #[cfg(test)]
    if debug_trace() {
        eprintln!(
            "[find_recurrer] u1=0x{:08x} u2=0x{:08x} u3=0x{:08x} geq_2_ranks=0x{:08x}",
            u1, u2, u3, geq_2_ranks
        );
    }

    // Card count = popcount of suit nibble (each card contributes one suit bit).
    let c1 = (u1 >> 12 & 0xF).count_ones();
    let c2 = (u2 >> 12 & 0xF).count_ones();
    let c3 = (u3 >> 12 & 0xF).count_ones();

    // bubble sort (u1,c1), (u2,c2), (u3,c3) by count DESC, rank ASC.
    let swap_12 = ((c1 > c2) as u32).wrapping_neg();
    let (p1, c1_s, p2, c2_s) = (
        (u1 & !swap_12) | (u2 & swap_12),
        (c1 & !swap_12) | (c2 & swap_12),
        (u2 & !swap_12) | (u1 & swap_12),
        (c2 & !swap_12) | (c1 & swap_12),
    );
    let swap_23 = ((c2_s > c3) as u32).wrapping_neg();
    let (p2, c2_s, p3, c3_s) = (
        (p2 & !swap_23) | (u3 & swap_23),
        (c2_s & !swap_23) | (c3 & swap_23),
        (u3 & !swap_23) | (p2 & swap_23),
        (c3 & !swap_23) | (c2_s & swap_23),
    );
    let swap_12_2 = ((c1_s > c2_s) as u32).wrapping_neg();
    let (p1, c1_s, p2, c2_s) = (
        (p1 & !swap_12_2) | (p2 & swap_12_2),
        (c1_s & !swap_12_2) | (c2_s & swap_12_2),
        (p2 & !swap_12_2) | (p1 & swap_12_2),
        (c2_s & !swap_12_2) | (c1_s & swap_12_2),
    );

    ((p1, p2, p3), (c1_s, c2_s, c3_s))
}

/// returns bitwise union of cards in flush if flush exists else 0_u32 w/o branching
///
/// Algorithm:
///     1. split cards into 4-arr of unions on suit via TZCNT trick
///     2. flush union | arr_element if >= 5 ones in rank bits of union via POPCNT + predicate mask trick
fn find_flush_union_branchless(cards: &[u32; 7]) -> u32 {
    let mut flushes = [0u32; 4];

    for c in cards {
        let idx = (*c >> 12).trailing_zeros() as usize; // TZCNT instruction on x86

        unsafe {
            // idx < 3 ensured by provided instance of Suit enum in card new impl
            *flushes.get_unchecked_mut(idx) |= c;
        }
    }

    let mut flush_union = 0u32;

    for flush in flushes {
        let rank_bits = flush & 0x1FFF_0000;

        let count = rank_bits.count_ones(); // POPCNT instruction on x86

        // 0x1111_1111 if count > 4 else 0x0000_0000 via two's compliment i32 repr
        let predicate_mask = ((4i32 - count as i32) >> 31) as u32;

        flush_union |= flush & predicate_mask;
    }

    flush_union
}

/// Returns r_seed_ext: seed bits for straight detection + top-card extraction.
/// Non-zero iff at least one straight exists. Branchless, no card accumulation.
///
/// Algorithm:
///     1. OR all cards to get 13-bit rank presence vector
///     2. extend w/ ace wheel bit at pos 0
///     3. sliding 5-bit AND window to find seeds of >=5 consecutive ranks
#[inline(always)]
fn find_straight_seed_branchless(cards: &[u32; 7]) -> u32 {
    let card_union: u32 =
        cards[0] | cards[1] | cards[2] | cards[3] | cards[4] | cards[5] | cards[6];
    let r_union = (card_union >> 16) & 0x1FFF;

    // "inject" ace bit at pos 0 for wheels
    let r_ext = (r_union << 1) | (r_union >> 12);
    // sliding window; 1 (seed) bits give starts of >= 5 card straights
    let r_seed_ext = r_ext & (r_ext >> 1) & (r_ext >> 2) & (r_ext >> 3) & (r_ext >> 4);

    #[cfg(test)]
    if debug_trace() {
        eprintln!(
            "[find_straight] r_union=0x{:04x} r_ext=0x{:04x} r_seed_ext=0x{:04x}",
            r_union, r_ext, r_seed_ext
        );
    }

    r_seed_ext
}

/// Returns the 5 cards forming the best (highest) straight, one per rank.
/// All zeros when no straight. Fully branchless.
///
/// r_seed_ext from find_straight_seed_branchless avoids recomputing straight union logic.
/// Highest seed = highest straight. In 7-card poker, the highest seed is always valid
/// (seed bits only exist where 5 consecutive ranks are present in the rank union).
///
/// Per-rank card extraction uses branchless max-select over all 7 cards.
/// Rank iteration is unrolled via 5x LSB extraction.
#[inline(always)]
fn find_top_straight_cards_branchless(cards: &[u32; 7], r_seed_ext: u32) -> [u32; 5] {
    // Branchless highest seed: LZCNT gives position of highest set bit.
    // When r_seed_ext == 0, leading_zeros() == 32, so shift produces 0 => top_seed = 0.
    let lz = r_seed_ext.leading_zeros(); // LZCNT: 1 cycle on x86
    let top_seed = 1u32.checked_shl(31u32.wrapping_sub(lz)).unwrap_or(0);

    // Expand seed to 5-bit run, un-extend back to rank positions
    let run_ext = top_seed | (top_seed << 1) | (top_seed << 2) | (top_seed << 3) | (top_seed << 4);
    let top_run = (run_ext >> 1) | ((run_ext & 1) << 12);

    // Mask: all-ones when straight exists, all-zeros otherwise
    let exists = ((r_seed_ext != 0) as u32).wrapping_neg();

    // Unrolled 5x LSB extraction to get individual rank one-hots
    let mut rb = top_run;
    let r0 = rb & (0u32.wrapping_sub(rb));
    rb ^= r0;
    let r1 = rb & (0u32.wrapping_sub(rb));
    rb ^= r1;
    let r2 = rb & (0u32.wrapping_sub(rb));
    rb ^= r2;
    let r3 = rb & (0u32.wrapping_sub(rb));
    rb ^= r3;
    let r4 = rb;

    // Shift to rank-bit positions for card matching
    let r0s = r0 << 16;
    let r1s = r1 << 16;
    let r2s = r2 << 16;
    let r3s = r3 << 16;
    let r4s = r4 << 16;

    /// Branchless max-select: find the highest card matching rank `$rs` across all 7 cards.
    /// For each card, predicate mask = 0xFFFFFFFF if card has this rank, else 0.
    /// Accumulate via: best = max(best, card) when match, else keep best.
    macro_rules! max_card_at_rank {
        ($rs:expr) => {{
            let mut best = 0u32;
            let mut i = 0;
            while i < 7 {
                let c = cards[i];
                let hit = ((c & $rs) != 0) as u32;
                let m = hit.wrapping_neg();
                // branchless max: if hit, take max(best, c); else keep best
                let gt = ((c > best) as u32).wrapping_neg();
                best = (best & !(m & gt)) | (c & m & gt);
                i += 1;
            }
            best & exists
        }};
    }

    let out = [
        max_card_at_rank!(r0s),
        max_card_at_rank!(r1s),
        max_card_at_rank!(r2s),
        max_card_at_rank!(r3s),
        max_card_at_rank!(r4s),
    ];

    #[cfg(test)]
    if debug_trace() {
        // Use hex: out may be [0,0,0,0,0] when no straight; transmuting to Card and displaying panics in suit()
        eprintln!(
            "[find_top_straight] r_seed_ext=0x{:04x} top_run=0x{:04x} best5=[0x{:08x} 0x{:08x} 0x{:08x} 0x{:08x} 0x{:08x}]",
            r_seed_ext, top_run, out[0], out[1], out[2], out[3], out[4]
        );
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::card::{Card, Rank, Suit};
    use crate::five::FiveHand;
    use itertools::Itertools;
    use std::str::FromStr;

    fn five_from_card_array(cards: [Card; 5]) -> FiveHand {
        // slow lol
        let s = format!(
            "{} {} {} {} {}",
            cards[0], cards[1], cards[2], cards[3], cards[4]
        );
        FiveHand::from_str(&s).unwrap()
    }

    /// Asserts best_five_branchless returns a hand with rank >= every possible 5-card subset
    fn assert_best_five_correct(seven: SevenHand) {
        let cards = seven.as_card_array();
        let best = seven.best_five_branchless();
        let best_rank = best.rank();

        for indices in (0..7).combinations(5) {
            let five_cards: [Card; 5] = [
                cards[indices[0]],
                cards[indices[1]],
                cards[indices[2]],
                cards[indices[3]],
                cards[indices[4]],
            ];
            let subset_hand = five_from_card_array(five_cards);
            assert!(
                best_rank >= subset_hand.rank(),
                "best_five_branchless rank {} should be >= subset rank {} for 7 cards {}",
                best_rank,
                subset_hand.rank(),
                seven
            );
        }
    }

    fn best(s: &str) -> SevenHand {
        SevenHand::from_str(s).unwrap()
    }

    // LLM generated tests warning: didnt fancy writing all these by hand

    #[test]
    fn test_best_five_1_1_royal_flush() {
        assert_eq!(
            best("Ah Kh Qh Jh Th 9h 8h").best_five_branchless().rank(),
            FiveHand::from_str("Ah Kh Qh Jh Th").unwrap().rank()
        );
    }
    #[test]
    fn test_best_five_1_2_straight_flush() {
        assert_best_five_correct(best("9h 8h 7h 6h 5h 4h 3h"));
    }
    #[test]
    fn test_best_five_1_3_four_of_a_kind() {
        assert_best_five_correct(best("Ac Ad Ah As Kc Qd Js"));
    }
    #[test]
    fn test_best_five_1_4_full_house() {
        assert_best_five_correct(best("Ts Td Th 7s 7c 2h 3d"));
    }
    #[test]
    fn test_best_five_1_5_flush() {
        assert_best_five_correct(best("Ah Jh 8h 4h 2h Kd 3c"));
    }
    #[test]
    fn test_best_five_1_6_straight() {
        assert_best_five_correct(best("9s 8h 7d 6c 5s 2h 3d"));
    }
    #[test]
    fn test_best_five_1_7_three_of_a_kind() {
        assert_best_five_correct(best("7s 7d 7h Kc 2s 3h 4d"));
    }
    #[test]
    fn test_best_five_1_8_two_pair() {
        assert_best_five_correct(best("As Ad Ks Kd 3h 2c 7d"));
    }
    #[test]
    fn test_best_five_1_9_pair() {
        assert_best_five_correct(best("As Ad Qh Jc 9s 8d 3h"));
    }
    #[test]
    fn test_best_five_1_10_high_card() {
        assert_best_five_correct(best("As Kc Jh 8d 3s 2h 7c"));
    }

    #[test]
    fn test_best_five_2_1_wheel() {
        assert_best_five_correct(best("Ah 2s 3d 4c 5h 9d Kc"));
    }
    #[test]
    fn test_best_five_2_3_seven_card_straight() {
        assert_best_five_correct(best("2h 3d 4s 5c 6h 7d 8s"));
    }
    #[test]
    fn test_best_five_2_4_six_card_straight() {
        assert_best_five_correct(best("3h 4d 5s 6c 7h 8d 2c"));
    }
    #[test]
    fn test_best_five_2_5_pair_in_straight() {
        assert_best_five_correct(best("9s 8h 7d 6c 5s 9h 9d"));
    }
    #[test]
    fn test_best_five_2_6_pair_in_straight_8high() {
        assert_best_five_correct(best("8s 7h 6d 5c 4s 8h 8d"));
    }
    #[test]
    fn test_best_five_2_7_pair_outside_straight() {
        assert_best_five_correct(best("9s 8h 7d 6c 5s Ah Ad"));
    }
    #[test]
    fn test_best_five_2_8_two_possible_straights() {
        assert_best_five_correct(best("6h 5d 4s 3c 2h 7d 8s"));
    }
    #[test]
    fn test_best_five_2_9_wheel_vs_six_high() {
        assert_best_five_correct(best("Ah 2h 3d 4c 5s 6h 7d"));
    }
    #[test]
    fn test_best_five_2_10_trips_in_straight() {
        assert_best_five_correct(best("9s 9h 9d 8c 7s 6h 5d"));
    }

    #[test]
    fn test_best_five_3_1_seven_card_sf() {
        assert_best_five_correct(best("3h 4h 5h 6h 7h 8h 9h"));
    }
    #[test]
    fn test_best_five_3_2_sf_plus_junk() {
        assert_best_five_correct(best("5s 6s 7s 8s 9s Ad Kc"));
    }
    #[test]
    fn test_best_five_3_3_royal_plus_lower_sf() {
        assert_best_five_correct(best("Th Jh Qh Kh Ah 2d 3c"));
    }
    #[test]
    fn test_best_five_3_4_wheel_sf() {
        assert_best_five_correct(best("Ac 2c 3c 4c 5c Kd Qh"));
    }
    #[test]
    fn test_best_five_3_5_sf_vs_higher_straight() {
        assert_best_five_correct(best("5d 6d 7d 8d 9d Ts Jh"));
    }
    #[test]
    fn test_best_five_3_7_sf_with_pair_in_ranks() {
        assert_best_five_correct(best("5h 6h 7h 8h 9h 9d 2c"));
    }
    #[test]
    fn test_best_five_3_8_six_card_sf() {
        assert_best_five_correct(best("2h 3h 4h 5h 6h 7h Kd"));
    }

    #[test]
    fn test_best_five_4_1_six_card_flush() {
        assert_best_five_correct(best("Ah Kh Qh Jh Th 9h 2d"));
    }
    #[test]
    fn test_best_five_4_3_flush_vs_straight() {
        assert_best_five_correct(best("Ah Kh Qh Jh 9h 8d 7c"));
    }
    #[test]
    fn test_best_five_4_4_flush_with_pair() {
        assert_best_five_correct(best("Ah Kh Qh Jh 9h 9d 2c"));
    }
    #[test]
    fn test_best_five_4_5_flush_with_two_pair() {
        assert_best_five_correct(best("Ah Kh Qh Jh 9h 9d Kc"));
    }

    #[test]
    fn test_best_five_5_2_trips_plus_two_pair() {
        assert_best_five_correct(best("As Ad Ah Ks Kd Kc 2h"));
    }
    #[test]
    fn test_best_five_5_3_quads_plus_pair() {
        assert_best_five_correct(best("Ac Ad Ah As Kc Kd 2h"));
    }
    #[test]
    fn test_best_five_5_6_fh_vs_two_pair() {
        assert_best_five_correct(best("2h 2d 2s 3c 3d As Kd"));
    }

    #[test]
    fn test_best_five_6_2_quads_plus_pair() {
        assert_best_five_correct(best("Ac Ad Ah As Kc Kd 2h"));
    }
    #[test]
    fn test_best_five_6_4_quads_vs_fh() {
        assert_best_five_correct(best("2c 2d 2h 2s As Ad Ah"));
    }

    #[test]
    fn test_best_five_7_2_two_pair_third_makes_fh() {
        assert_best_five_correct(best("As Ad Ks Kd Kh 2c 7d"));
    }
    #[test]
    fn test_best_five_7_3_three_pair() {
        assert_best_five_correct(best("As Ad Ks Kd Qh Qc 2d"));
    }
    #[test]
    fn test_best_five_7_5_two_pair_kicker() {
        assert_best_five_correct(best("As Ad Ks Kd 7h 6c 2d"));
    }

    #[test]
    fn test_best_five_8_2_pair_plus_straight() {
        assert_best_five_correct(best("9s 8h 7d 6c 5s As Ad"));
    }
    #[test]
    fn test_best_five_8_4_trips_plus_pair() {
        assert_best_five_correct(best("7s 7d 7h Kc Kd 2s 3h"));
    }

    #[test]
    fn test_best_five_10_3_three_pair_makes_fh() {
        assert_best_five_correct(best("As Ad Ks Kd Qh Qc 2d"));
    }
    #[test]
    fn test_best_five_10_4_quads_vs_fh() {
        assert_best_five_correct(best("Ac Ad Ah As Kc Kd 2h"));
    }

    #[test]
    fn test_best_five_12_2_six_cards_one_suit() {
        assert_best_five_correct(best("Ah Kh Qh Jh Th 9h 2d"));
    }
    #[test]
    fn test_best_five_12_3_seven_cards_one_suit() {
        assert_best_five_correct(best("2c 3c 5c 7c 9c Jc Kc"));
    }

    #[test]
    fn test_best_five_debug_trace() {
        let f = best("2h 3d 4s 5c 6h 7d 8s").best_five_branchless();
        let p = best("9s 8h 7d 6c 5s 2h 3d").best_five_branchless();
        let _ = (f, p);
    }

    #[test]
    fn test_best_five_exhaustive() {
        for hand in [
            "Ah Kh Qh Jh Th 9h 8h",
            "Ac Ad Ah As Kc Qd Js",
            "Ts Td Th 7s 7c 2h 3d",
            "2c 3c 5c 7c 9c Jd Ks",
            "2h 3d 4s 5c 6h 7d 8s",
            "9s 8h 7d 6c 5s 9h 9d",
            "8s 7h 6d 5c 4s 8h 8d",
            "2h 2d 2s 3c 4h 5d 6s",
            "Ah Ac Kd Ks 3h 4c 5d",
            "Qh Qd As Kc Jd 9s 2h",
            "As Kd Qc Jh 9h 7d 3c",
        ] {
            assert_best_five_correct(best(hand));
        }
    }
}
