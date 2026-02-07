pub mod card;
pub mod five;
mod seven;

mod generated {
    include!(concat!(env!("OUT_DIR"), "/codegen.rs"));
}

#[cfg(test)]
mod tests {
    use super::*;
    use five::FiveHand;
    use std::str::FromStr;

    #[test]
    fn assert_hash_lengths() {
        // lengths via doing the combinatorics by hand
        // use http://suffe.cool/poker/7462.html if you cant count ;)
        assert_eq!(generated::FIVE_FLUSH_HASH.len(), 1287);
        assert_eq!(generated::FIVE_NONFLUSH_HASH.len(), 6175);
    }

    #[test]
    fn assert_rank_dummy_cases() {   
        let royal_flush = FiveHand::from_str("As Ks Qs Js Ts").unwrap();
        let straight_flush = FiveHand::from_str("9h 8h 7h 6h 5h").unwrap();
        let four_of_a_kind = FiveHand::from_str("Ac Ad Ah As Kc").unwrap();
        let full_house = FiveHand::from_str("Ts Td Th 7s 7c").unwrap();
        let flush = FiveHand::from_str("Ah Jh 8h 4h 2h").unwrap();
        let straight = FiveHand::from_str("9s 8h 7d 6c 5s").unwrap();
        let three_of_a_kind = FiveHand::from_str("7s 7d 7h Kc 2s").unwrap();
        let two_pair = FiveHand::from_str("As Ad Ks Kd 3h").unwrap();
        let pair = FiveHand::from_str("As Ad Qh Jc 9s").unwrap();
        let high_card = FiveHand::from_str("As Kc Jh 8d 3s").unwrap();
        let worst_hand = FiveHand::from_str("7h 5d 4h 3d 2h").unwrap();

        assert_eq!(worst_hand.rank(), 1, "There are worse hands??? ruhuhoh scoobs");

        assert!(royal_flush.rank() > straight_flush.rank());
        assert!(straight_flush.rank() > four_of_a_kind.rank());
        assert!(four_of_a_kind.rank() > full_house.rank());
        assert!(full_house.rank() > flush.rank());
        assert!(flush.rank() > straight.rank());
        assert!(straight.rank() > three_of_a_kind.rank());
        assert!(three_of_a_kind.rank() > two_pair.rank());
        assert!(two_pair.rank() > pair.rank());
        assert!(pair.rank() > high_card.rank());

        let royal_flush_diamonds = FiveHand::from_str("Ad Kd Qd Jd Td").unwrap();
        assert_eq!(royal_flush.rank(), royal_flush_diamonds.rank());

        let straight_mixed_order = FiveHand::from_str("8h 6c 9s 5s 7d").unwrap();
        assert_eq!(straight.rank(), straight_mixed_order.rank());
    }
}
