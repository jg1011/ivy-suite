//! generate prime product -> rank lookup tables
//! CactusKev ranks lowest=best; I'm based and can count so I've done highest=best

use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use itertools::Itertools;
use phf_codegen;

/// Number of straight flush equiv classes = # cards A..=5 = 10
const NUM_STRAIGHT_FLUSH_FIVE_CARD_CLASSES: u32 = 10;
/// Number of quads equiv classes = 13C2 * 2 = 156
const NUM_QUADS_FIVE_CARD_CLASSES: u32 = 156;
/// Number of full house equiv classes = 13C2 * 2 = 156
const NUM_FULL_HOUSE_FIVE_CARD_CLASSES: u32 = 156;
/// Number of flush equiv classes = 13C5 - 10 = 1277
const NUM_FLUSH_FIVE_CARD_CLASSES: u32 = 1277;
/// Number of straight equiv classes = # cards A..=5 = 10
const NUM_STRAIGHT_FIVE_CARD_CLASSES: u32 = 10;
/// Number of trips equiv classes = 13 * 12C2 = 858
const NUM_TRIPS_FIVE_CARD_CLASSES: u32 = 858;
/// Number of two pair equivalence classes = 13C2 * 11 = 858
const NUM_TWO_PAIR_FIVE_CARD_CLASSES: u32 = 858;
/// Number of pair equivlance classes = 13 * 12C3 = 2860
const NUM_PAIR_FIVE_CARD_CLASSES: u32 = 2860;
/// Number of high card equivalnce classes = 13C5 - 10 = 1277
const NUM_HIGH_CARD_FIVE_CARD_CLASSES: u32 = 1277;
/// Total number of 5-card poker hand equivalence hands
const NUM_FIVE_CARD_CLASSES: u32 = NUM_HIGH_CARD_FIVE_CARD_CLASSES
    + NUM_PAIR_FIVE_CARD_CLASSES
    + NUM_TWO_PAIR_FIVE_CARD_CLASSES
    + NUM_TRIPS_FIVE_CARD_CLASSES
    + NUM_STRAIGHT_FIVE_CARD_CLASSES
    + NUM_FLUSH_FIVE_CARD_CLASSES
    + NUM_FULL_HOUSE_FIVE_CARD_CLASSES
    + NUM_QUADS_FIVE_CARD_CLASSES
    + NUM_STRAIGHT_FLUSH_FIVE_CARD_CLASSES;

/// First 13 primes; w/ prime_i being the prime repr of the card with rank i (two low, ace high)
const PRIMES: [u32; 13] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41];

/// (prime_product, rank) pair vec for flush hands
fn gen_flush_map_entry_vec() -> Vec<(u32, u32)> {
    let mut hand_rank = NUM_FIVE_CARD_CLASSES;
    let mut entries = Vec::<(u32, u32)>::new();

    // straight flushes
    for i in (3..=12_i8).rev() {
        // 12 = Rank::Ace & 4 = Rank::Six
        entries.push((
            PRIMES[i as usize]
                * PRIMES[(i - 1) as usize]
                * PRIMES[(i - 2) as usize]
                * PRIMES[(i - 3) as usize]
                * PRIMES[(i - 4).rem_euclid(13) as usize], // (-1) mod (13) == 12 -- wraps wheel
            hand_rank,
        ));
        hand_rank -= 1;
    }

    hand_rank -= NUM_QUADS_FIVE_CARD_CLASSES;
    hand_rank -= NUM_FULL_HOUSE_FIVE_CARD_CLASSES;

    // flushes
    // <T: Itertools>.combinations returns in lexicographical ascending
    for r in (0..=12_usize).rev().combinations(5) {
        let is_std_straight =
            r[0] == (r[1] + 1) && r[0] == (r[2] + 2) && r[0] == (r[3] + 3) && r[0] == (r[4] + 4);
        let is_wheel = r[0] == 12 && r[1] == 3 && r[2] == 2 && r[3] == 1 && r[4] == 0; // raaaasclart....
        if !(is_std_straight || is_wheel) {
            entries.push((
                PRIMES[r[0]] * PRIMES[r[1]] * PRIMES[r[2]] * PRIMES[r[3]] * PRIMES[r[4]],
                hand_rank,
            ));
            hand_rank -= 1;
        }
    }

    entries
}

/// (prime_product, rank) pair vec for non-flush hands
fn gen_non_flush_map_entry_vec() -> Vec<(u32, u32)> {
    let mut hand_rank: u32 = NUM_FIVE_CARD_CLASSES;
    let mut entries = Vec::<(u32, u32)>::new();

    hand_rank -= NUM_STRAIGHT_FLUSH_FIVE_CARD_CLASSES;

    // quads
    for i in (0..=12).rev() {
        for j in (0..=12).rev() {
            if i == j {
                continue;
            }
            entries.push((PRIMES[i].pow(4) * PRIMES[j], hand_rank));
            hand_rank -= 1;
        }
    }

    // full houses
    for i in (0..=12).rev() {
        for j in (0..=12).rev() {
            if i == j {
                continue;
            }
            entries.push((PRIMES[i].pow(3) * PRIMES[j].pow(2), hand_rank));
            hand_rank -= 1;
        }
    }

    hand_rank -= NUM_FLUSH_FIVE_CARD_CLASSES;

    // straights
    for i in (3..=12_i8).rev() {
        // 12 = Rank::Ace & 3 = Rank::Five
        entries.push((
            PRIMES[i as usize]
                * PRIMES[(i - 1) as usize]
                * PRIMES[(i - 2) as usize]
                * PRIMES[(i - 3) as usize]
                * PRIMES[(i - 4).rem_euclid(13) as usize], // (-1) mod (13) == 12 -- only wraps wheel, identity elsewhere
            hand_rank,
        ));
        hand_rank -= 1;
    }

    // trips
    for i in (0..=12).rev() {
        for kickers in (0..=12).rev().combinations(2) {
            if kickers.contains(&i) {
                continue;
            }
            entries.push((
                PRIMES[i].pow(3) * PRIMES[kickers[0]] * PRIMES[kickers[1]],
                hand_rank,
            ));
            hand_rank -= 1;
        }
    }

    // two-pairs
    for pairs in (0..=12).rev().combinations(2) {
        let (p1, p2) = (pairs[0], pairs[1]);
        for kicker in (0..=12).rev() {
            if kicker == p1 || kicker == p2 {
                continue;
            }
            entries.push((
                PRIMES[p1].pow(2) * PRIMES[p2].pow(2) * PRIMES[kicker],
                hand_rank,
            ));
            hand_rank -= 1;
        }
    }

    // pairs
    for i in (0..=12_usize).rev() {
        for kickers in (0..=12_usize).rev().combinations(3) {
            if kickers.contains(&i) {
                continue;
            }
            entries.push((
                PRIMES[i].pow(2) * PRIMES[kickers[0]] * PRIMES[kickers[1]] * PRIMES[kickers[2]],
                hand_rank,
            ));
            hand_rank -= 1;
        }
    }

    // high cards
    // <T: Itertools>.combinations returns in lexicographical ascending
    for r in (0..=12).rev().combinations(5) {
        if r[0] < 5 {
            // cheeky micro-optimisation
            break;
        }
        let is_std_straight =
            r[0] == (r[1] + 1) && r[0] == (r[2] + 2) && r[0] == (r[3] + 3) && r[0] == (r[4] + 4);
        let is_wheel = r[0] == 12 && r[1] == 3 && r[2] == 2 && r[3] == 1 && r[4] == 0; // raaaasclart....
        if !(is_wheel || is_std_straight) {
            entries.push((
                PRIMES[r[0] as usize] // surely theres a less verbose way of usize downcasting here
                    * PRIMES[r[1] as usize]
                    * PRIMES[r[2] as usize]
                    * PRIMES[r[3] as usize]
                    * PRIMES[r[4] as usize],
                hand_rank,
            ));
            hand_rank -= 1;
        }
    }

    entries
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs"); // rerun on change

    let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    let mut file = BufWriter::new(File::create(&path).unwrap());

    let mut flush_map = phf_codegen::Map::new();
    let mut non_flush_map = phf_codegen::Map::new();

    let flush_entries = gen_flush_map_entry_vec();
    let non_flush_entries = gen_non_flush_map_entry_vec();

    // codegen takes string value and writes explicitly in codegen.rs w/ relevant typecasting
    for (key, value) in flush_entries {
        flush_map.entry(key, value.to_string());
    }
    for (key, value) in non_flush_entries {
        non_flush_map.entry(key, value.to_string());
    }

    writeln!(
        &mut file,
        "pub static FIVE_FLUSH_HASH: phf::Map<u32, u32> = {};",
        flush_map.build()
    )
    .unwrap();

    writeln!(
        &mut file,
        "pub static FIVE_NONFLUSH_HASH: phf::Map<u32, u32> = {};",
        non_flush_map.build()
    )
    .unwrap();
}
