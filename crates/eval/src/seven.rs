#![allow(unused)]

use crate::card::Card;

#[derive(Clone, Copy)]
#[repr(transparent)] // enforce layout = [Card; 7] = [u32; 7]
pub struct SevenHand([Card; 7]);