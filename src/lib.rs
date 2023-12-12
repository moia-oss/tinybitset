//! TODO
use std::array;
use std::iter;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::Not;

use num_traits::PrimInt;

/// Integer that can be used as a block of bits in a bitset.
pub trait BitBlock: PrimInt + BitAndAssign + BitOrAssign + 'static {
    /// Number of bits in the block.
    const BITS: usize;

    /// Block without any bits set, aka `0`.
    const EMPTY: Self;

    /// Block with only the least significant bit set, aka `1`.
    const LSB: Self;

    /// Block with all bits set.
    const ALL: Self;
}

macro_rules! impl_bit_block {
    ($($int:ty),*) => {
        $(
            impl BitBlock for $int {
                const BITS: usize = <$int>::BITS as usize;
                const EMPTY: Self = 0;
                const LSB: Self = 1;
                const ALL: Self = <$int>::MAX;
            }
        )*
    };
}

impl_bit_block!(u8, u16, u32, u64, u128);

/// TODO
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InlineBitSet<T: BitBlock, const N: usize> {
    blocks: [T; N],
}

#[cfg(test)]
mod tests {}
