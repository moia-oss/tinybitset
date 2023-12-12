use std::array;
use std::iter;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::Not;

use num_traits::PrimInt;

/// Integer that can be used as a block of bits in a bitset.
pub trait Block: PrimInt + BitAndAssign + BitOrAssign + 'static {
    const BITS: usize;
    const ZERO: Self;
    const ONE: Self;
    const MAX: Self;
}

macro_rules! impl_block {
    ($($t:ty),*) => {
        $(
            impl Block for $t {
                const BITS: usize = <$t>::BITS as usize;
                const ZERO: Self = 0;
                const ONE: Self = 1;
                const MAX: Self = <$t>::MAX;
            }
        )*
    };
}

impl_block!(u8, u16, u32, u64, u128);

/// Bitset storing `N` blocks of type `T` inline.
#[derive(Debug, Clone, Copy)]
pub struct BitSet<T: Block, const N: usize>([T; N]);

impl<T: Block, const N: usize> BitSet<T, N> {
    pub const LEN: usize = N * T::BITS;
    pub const EMPTY: Self = Self([T::ZERO; N]);
    pub const ALL: Self = Self([T::MAX; N]);

    /// Creates a bitset with only the bit at `index` set.
    #[inline]
    pub fn single(index: usize) -> Self {
        assert!(index < Self::LEN, "index out of bounds");
        let mut blocks = [T::ZERO; N];
        let block_index = index / T::BITS;
        let index_in_block = index % T::BITS;
        blocks[block_index] |= T::ONE << index_in_block;
        Self(blocks)
    }

    pub fn iter(self) -> impl Iterator<Item = usize> {
        self.0
            .into_iter()
            .enumerate()
            .flat_map(|(block_index, mut block)| {
                iter::from_fn(move || {
                    if block == T::ZERO {
                        None
                    } else {
                        let index_in_block = block.trailing_zeros() as usize;
                        block &= !(T::one() << index_in_block);
                        Some(block_index * T::BITS + index_in_block)
                    }
                })
            })
    }
}

impl<T: Block, const N: usize> FromIterator<usize> for BitSet<T, N> {
    fn from_iter<I: IntoIterator<Item = usize>>(iter: I) -> Self {
        iter.into_iter()
            .map(Self::single)
            .fold(Self::EMPTY, BitOr::bitor)
    }
}

impl<T: Block, const N: usize> BitAnd for BitSet<T, N> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(array::from_fn(|i| self.0[i] & rhs.0[i]))
    }
}

impl<T: Block, const N: usize> BitAndAssign for BitSet<T, N> {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl<T: Block, const N: usize> BitOr for BitSet<T, N> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(array::from_fn(|i| self.0[i] | rhs.0[i]))
    }
}

impl<T: Block, const N: usize> BitOrAssign for BitSet<T, N> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl<T: Block, const N: usize> Not for BitSet<T, N> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(self.0.map(|block| !block))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiple_blocks() {
        let expected = vec![0, 42, 128, 255];
        let bitset = expected.iter().copied().collect::<BitSet<u128, 2>>();
        let actual: Vec<_> = bitset.iter().collect();
        assert_eq!(actual, expected);
    }
}
