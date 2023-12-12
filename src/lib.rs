//! TODO
use std::array;
use std::fmt;
use std::fmt::Binary;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::LowerHex;
use std::fmt::UpperHex;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Not;

use num_traits::PrimInt;

/// Integer that can be used as a block of bits in a bitset.
pub trait BitBlock: PrimInt + Binary + LowerHex + UpperHex + 'static {
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

            impl From<InlineBitSet<$int, 1>> for $int {
                /// Convert the bitset into the underlying bit block.
                ///
                /// Due to the orphan rule, this cannot be covered by a blanket implementation and
                /// is thus separately implemented for all primitive integer types.
                fn from(bitset: InlineBitSet<$int, 1>) -> Self {
                    bitset.blocks[0]
                }
            }
        )*
    };
}

impl_bit_block!(u8, u16, u32, u64, u128);

/// TODO
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InlineBitSet<T: BitBlock, const N: usize> {
    blocks: [T; N],
}

impl<T: BitBlock, const N: usize> InlineBitSet<T, N> {
    /// Number of bits in the bitset.
    pub const CAPACITY: usize = T::BITS * N;

    /// Bitset with no bits set.
    pub const EMPTY: Self = Self {
        blocks: [T::EMPTY; N],
    };

    /// Bitset with all bits set.
    pub const ALL: Self = Self {
        blocks: [T::ALL; N],
    };

    /// Number of bits in the bitset.
    ///
    /// Equivalent to [`Self::CAPACITY`].
    pub const fn capacity(self) -> usize {
        Self::CAPACITY
    }
}

impl<T: BitBlock, const N: usize> Default for InlineBitSet<T, N> {
    /// Returns [`Self::EMPTY`].
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<T: BitBlock, const N: usize> From<[T; N]> for InlineBitSet<T, N> {
    /// Create a bitset from the underlying bit blocks.
    ///
    /// See [`InlineBitSet`] for more information on how the bits are indexed.
    fn from(blocks: [T; N]) -> Self {
        Self { blocks }
    }
}

impl<T: BitBlock, const N: usize> From<InlineBitSet<T, N>> for [T; N] {
    /// Convert the bitset into the underlying bit blocks.
    ///
    /// See [`InlineBitSet`] for more information on how the bits are indexed.
    fn from(bitset: InlineBitSet<T, N>) -> Self {
        bitset.blocks
    }
}

impl<T: BitBlock> From<T> for InlineBitSet<T, 1> {
    /// Create a bitset from the underlying bit block.
    fn from(block: T) -> Self {
        Self { blocks: [block] }
    }
}

impl<T: BitBlock, const N: usize> Not for InlineBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits flipped.
    fn not(self) -> Self::Output {
        array::from_fn(|i| !self.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitAnd for InlineBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits that are set in both `self` and `rhs`.
    fn bitand(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.blocks[i] & rhs.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitAndAssign for InlineBitSet<T, N> {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl<T: BitBlock, const N: usize> BitOr for InlineBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits that are set in either `self` or `rhs`.
    fn bitor(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.blocks[i] | rhs.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitOrAssign for InlineBitSet<T, N> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl<T: BitBlock, const N: usize> BitXor for InlineBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits that are set in exactly one of `self` and `rhs`.
    fn bitxor(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.blocks[i] ^ rhs.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitXorAssign for InlineBitSet<T, N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl<T: BitBlock, const N: usize> Debug for InlineBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "InlineBitSet([")?;
        for (i, block) in self.blocks.into_iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }

            // The `+ 2` accounts for the `0b` prefix
            write!(f, "{block:#0width$b}", width = T::BITS + 2)?;
        }
        write!(f, "])")
    }
}

impl<T: BitBlock, const N: usize> Display for InlineBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Binary::fmt(self, f)
    }
}

impl<T: BitBlock, const N: usize> Binary for InlineBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0b")?;
        }

        for block in self.blocks.iter().rev() {
            write!(f, "{block:0width$b}", width = T::BITS)?;
        }

        Ok(())
    }
}

impl<T: BitBlock, const N: usize> LowerHex for InlineBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }

        for block in self.blocks.iter().rev() {
            write!(f, "{block:0width$x}", width = T::BITS / 4)?;
        }

        Ok(())
    }
}

impl<T: BitBlock, const N: usize> UpperHex for InlineBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "0x")?;
        }

        for block in self.blocks.iter().rev() {
            write!(f, "{block:0width$X}", width = T::BITS / 4)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Default bit set for testing
    type TestBitSet = InlineBitSet<u8, 2>;

    #[test]
    fn capacity() {
        fn test_both<T: BitBlock, const N: usize>(expected: usize) {
            assert_eq!(expected, InlineBitSet::<T, N>::CAPACITY);
            assert_eq!(expected, InlineBitSet::<T, N>::default().capacity());
        }

        test_both::<u8, 1>(8);
        test_both::<u16, 1>(16);
        test_both::<u32, 1>(32);
        test_both::<u64, 1>(64);
        test_both::<u128, 1>(128);

        test_both::<u16, 3>(48);
        test_both::<u128, 8>(1024);
    }

    #[test]
    fn empty() {
        assert_eq!(
            TestBitSet::from([0b0000_0000, 0b0000_0000]),
            TestBitSet::EMPTY
        );
    }

    #[test]
    fn all() {
        assert_eq!(
            TestBitSet::from([0b1111_1111, 0b1111_1111]),
            TestBitSet::ALL
        );
    }

    #[test]
    fn from_into() {
        let blocks = [0b1010_1010, 0b0101_0101];
        assert_eq!(blocks, <[_; 2]>::from(TestBitSet::from(blocks)));
    }

    #[test]
    fn from_into_integer() {
        fn test<T>(x: T)
        where
            T: Debug + BitBlock + From<InlineBitSet<T, 1>>,
        {
            assert_eq!(x, InlineBitSet::from(x).into());
        }

        test(0x42_u8);
        test(0x1EE7_u16);
        test(0xDEAD_BEEF_u32);
        test(0x0123_4567_89AB_CDEF_u64);
        test(0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210_u128);
    }

    #[test]
    fn default() {
        assert_eq!(TestBitSet::EMPTY, TestBitSet::default());
    }

    #[test]
    fn not() {
        assert_eq!(TestBitSet::ALL, !TestBitSet::EMPTY);
        assert_eq!(TestBitSet::EMPTY, !TestBitSet::ALL);
        assert_eq!(
            TestBitSet::from([0b00111100, 0b10101010]),
            !TestBitSet::from([0b11000011, 0b01010101])
        );
    }

    #[test]
    fn and() {
        fn test(mut l: TestBitSet, r: TestBitSet, expected: TestBitSet) {
            assert_eq!(expected, l & r);
            l &= r;
            assert_eq!(expected, l);
        }

        test(TestBitSet::EMPTY, TestBitSet::EMPTY, TestBitSet::EMPTY);
        test(TestBitSet::ALL, TestBitSet::EMPTY, TestBitSet::EMPTY);
        test(TestBitSet::EMPTY, TestBitSet::ALL, TestBitSet::EMPTY);
        test(TestBitSet::ALL, TestBitSet::ALL, TestBitSet::ALL);

        test(
            TestBitSet::from([0b11100111, 0b01010101]),
            TestBitSet::from([0b00111100, 0b10101010]),
            TestBitSet::from([0b00100100, 0b00000000]),
        );
    }

    #[test]
    fn or() {
        fn test(mut l: TestBitSet, r: TestBitSet, expected: TestBitSet) {
            assert_eq!(expected, l | r);
            l |= r;
            assert_eq!(expected, l);
        }

        test(TestBitSet::EMPTY, TestBitSet::EMPTY, TestBitSet::EMPTY);
        test(TestBitSet::ALL, TestBitSet::EMPTY, TestBitSet::ALL);
        test(TestBitSet::EMPTY, TestBitSet::ALL, TestBitSet::ALL);
        test(TestBitSet::ALL, TestBitSet::ALL, TestBitSet::ALL);

        test(
            TestBitSet::from([0b01100110, 0b01010101]),
            TestBitSet::from([0b00111100, 0b10101010]),
            TestBitSet::from([0b01111110, 0b11111111]),
        );
    }

    #[test]
    fn xor() {
        fn test(mut l: TestBitSet, r: TestBitSet, expected: TestBitSet) {
            assert_eq!(expected, l ^ r);
            l ^= r;
            assert_eq!(expected, l);
        }

        test(TestBitSet::EMPTY, TestBitSet::EMPTY, TestBitSet::EMPTY);
        test(TestBitSet::ALL, TestBitSet::EMPTY, TestBitSet::ALL);
        test(TestBitSet::EMPTY, TestBitSet::ALL, TestBitSet::ALL);
        test(TestBitSet::ALL, TestBitSet::ALL, TestBitSet::EMPTY);

        test(
            TestBitSet::from([0b01100110, 0b01010101]),
            TestBitSet::from([0b00111100, 0b10101010]),
            TestBitSet::from([0b01011010, 0b11111111]),
        );
    }

    #[test]
    fn debug_formatting() {
        assert_eq!(
            "InlineBitSet([0b00000000, 0b00000000])",
            format!("{:?}", TestBitSet::EMPTY)
        );
        assert_eq!(
            "InlineBitSet([0b11111111, 0b11111111])",
            format!("{:?}", TestBitSet::ALL)
        );
        assert_eq!(
            "InlineBitSet([0b01010101, 0b10101010])",
            format!("{:?}", TestBitSet::from([0b0101_0101, 0b1010_1010]))
        );

        assert_eq!(
            "InlineBitSet([0b00111100])",
            format!("{:#?}", InlineBitSet::from(0b0011_1100_u8))
        );
    }

    #[test]
    fn display_formatting() {
        assert_eq!("0000000000000000", TestBitSet::EMPTY.to_string());
        assert_eq!("1111111111111111", TestBitSet::ALL.to_string());
        assert_eq!(
            "1111000000001111",
            TestBitSet::from([0b0000_1111, 0b1111_0000]).to_string()
        );
    }

    #[test]
    fn binary_formatting() {
        assert_eq!("0000000000000000", format!("{:b}", TestBitSet::EMPTY));
        assert_eq!("0b0000000000000000", format!("{:#b}", TestBitSet::EMPTY));
        assert_eq!("1111111111111111", format!("{:b}", TestBitSet::ALL));
        assert_eq!(
            "1111000000001111",
            format!("{:b}", TestBitSet::from([0b0000_1111, 0b1111_0000]))
        );
    }

    #[test]
    fn lower_hex_formatting() {
        assert_eq!("0000", format!("{:x}", TestBitSet::EMPTY));
        assert_eq!("0x0000", format!("{:#x}", TestBitSet::EMPTY));
        assert_eq!("ffff", format!("{:x}", TestBitSet::ALL));
        assert_eq!("e71e", format!("{:x}", TestBitSet::from([0x1e, 0xe7])));
    }

    #[test]
    fn upper_hex_formatting() {
        assert_eq!("0000", format!("{:X}", TestBitSet::EMPTY));
        assert_eq!("0x0000", format!("{:#X}", TestBitSet::EMPTY));
        assert_eq!("FFFF", format!("{:X}", TestBitSet::ALL));
        assert_eq!("E71E", format!("{:X}", TestBitSet::from([0x1E, 0xE7])));
    }
}
