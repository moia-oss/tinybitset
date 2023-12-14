//! This crate provides a small, fixed size [bitset type](TinyBitSet) that
//! stores its data inline rather than on the heap.
//!
//! Bitsets are a data structure that can be viewed through two lenses:
//!
//! - As an array of booleans that is stored in a compressed fashion using a
//!   single bit per boolean.
//! - As a set of small integers from the range `[0, n)`, where `n` is the
//!   number of bits used in the bitset.
//!
//! This crate supports functionality for both of these views but specializes on
//! use-cases where only a small number of bits are needed with an upper-bound
//! known beforehand. The [`TinyBitSet`] is copyable and the implementation
//! assumes in many places that the data is small enough to cheaply be copied.
//! Thus it is mostly suitable for sizes of up to 256 bits. For larger sizes, a
//! heap-allocated crate like [`fixedbitset`][fixedbitset] is likely a better fit.
//!
//! One unique feature of this crate is that it uses const generics to have a
//! single generic bitset type whose size and underlying storage type can be
//! chosen with generic arguments. This also allows writing algorithms that are
//! generic over these parameters and thus can use a different bitset size
//! depending on the use-case.
//!
//! [fixedbitset]: https://github.com/petgraph/fixedbitset
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
use std::ops::Index;
use std::ops::Not;

use num_traits::PrimInt;

/// Integer that can be used as a block of bits in a bitset.
pub trait BitBlock:
    PrimInt + BitAndAssign + BitOrAssign + BitXorAssign + Binary + LowerHex + UpperHex + 'static
{
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

            impl From<TinyBitSet<$int, 1>> for $int {
                /// Convert the bitset into the underlying bit block.
                ///
                /// Due to the orphan rule, this cannot be covered by a blanket implementation and
                /// is thus separately implemented for all primitive integer types.
                fn from(bitset: TinyBitSet<$int, 1>) -> Self {
                    bitset.blocks[0]
                }
            }
        )*
    };
}

impl_bit_block!(u8, u16, u32, u64, u128);

/// A small, fixed size bitset that stores its data inline.
///
/// # Storage and indexing
///
/// The bitsets storage consists of `N` blocks of type `T`, where `T` is any of
/// the unsigned integer types implementing [`BitBlock`]. Thus, the bitset has a
/// fixed size of `T::BITS * N` bits can be freely converted to and from the
/// array of blocks.
///
/// The bits are indexed from front to back within the array of blocks, and from
/// least significant to most significant within each block. Thus, the bit with
/// index `i` is stored in the `(i / T::BITS)`-th block in the `(i %
/// T::BITS)`-th least significant bit.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TinyBitSet<T: BitBlock, const N: usize> {
    blocks: [T; N],
}

impl<T: BitBlock, const N: usize> TinyBitSet<T, N> {
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

    /// Creates an empty bitset.
    ///
    /// Equivalent to [`Self::EMPTY`].
    pub const fn new() -> Self {
        Self::EMPTY
    }

    /// Creates a bitset with exactly one bit set.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    pub fn singleton(bit: usize) -> Self {
        Self::new().inserted(bit)
    }

    /// Number of bits in the bitset.
    ///
    /// Equivalent to [`Self::CAPACITY`].
    pub const fn capacity(self) -> usize {
        Self::CAPACITY
    }

    /// Counts the number of bits that are set.
    pub fn len(self) -> usize {
        self.blocks
            .into_iter()
            .map(|block| block.count_ones() as usize)
            .sum()
    }

    /// Returns whether no bits are set.
    pub fn is_empty(self) -> bool {
        self.blocks.iter().all(|&block| block == T::EMPTY)
    }

    /// Set the given bit.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    pub fn insert(&mut self, bit: usize) {
        self.blocks[bit / T::BITS] |= T::LSB << (bit % T::BITS);
    }

    /// Return a new bitset with the given bit set.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    #[must_use]
    pub fn inserted(mut self, bit: usize) -> Self {
        self.insert(bit);
        self
    }

    /// Unset the given bit.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    pub fn remove(&mut self, bit: usize) {
        self.blocks[bit / T::BITS] &= !(T::LSB << (bit % T::BITS));
    }

    /// Return a new bitset with the given bit unset.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    #[must_use]
    pub fn removed(mut self, bit: usize) -> Self {
        self.remove(bit);
        self
    }

    /// Flip the given bit.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    pub fn toggle(&mut self, bit: usize) {
        self.blocks[bit / T::BITS] ^= T::LSB << (bit % T::BITS);
    }

    /// Return a new bitset with the given bit flipped.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    #[must_use]
    pub fn toggled(mut self, bit: usize) -> Self {
        self.toggle(bit);
        self
    }

    /// Sets the given bit to the given value.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    pub fn assign(&mut self, bit: usize, value: bool) {
        if value {
            self.insert(bit);
        } else {
            self.remove(bit);
        }
    }

    /// Return a new bitset with the given bit set to the given value.
    ///
    /// # Panics
    ///
    /// Panics if `bit >= Self::CAPACITY`.
    #[must_use]
    pub fn assigned(mut self, bit: usize, value: bool) -> Self {
        self.assign(bit, value);
        self
    }
}

impl<T: BitBlock, const N: usize> Default for TinyBitSet<T, N> {
    /// Returns [`Self::EMPTY`].
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<T: BitBlock, const N: usize> From<[T; N]> for TinyBitSet<T, N> {
    /// Create a bitset from the underlying bit blocks.
    ///
    /// See [`TinyBitSet`] for more information on how the bits are indexed.
    fn from(blocks: [T; N]) -> Self {
        Self { blocks }
    }
}

impl<T: BitBlock, const N: usize> From<TinyBitSet<T, N>> for [T; N] {
    /// Convert the bitset into the underlying bit blocks.
    ///
    /// See [`TinyBitSet`] for more information on how the bits are indexed.
    fn from(bitset: TinyBitSet<T, N>) -> Self {
        bitset.blocks
    }
}

impl<T: BitBlock> From<T> for TinyBitSet<T, 1> {
    /// Create a bitset from the underlying bit block.
    fn from(block: T) -> Self {
        Self { blocks: [block] }
    }
}

impl<T: BitBlock, const N: usize> Index<usize> for TinyBitSet<T, N> {
    type Output = bool;

    fn index(&self, index: usize) -> &Self::Output {
        if (self.blocks[index / T::BITS] >> (index % T::BITS)) & T::LSB == T::LSB {
            &true
        } else {
            &false
        }
    }
}

impl<T: BitBlock, const N: usize> Not for TinyBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits flipped.
    fn not(self) -> Self::Output {
        array::from_fn(|i| !self.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitAnd for TinyBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits that are set in both `self` and `rhs`.
    fn bitand(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.blocks[i] & rhs.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitAndAssign for TinyBitSet<T, N> {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl<T: BitBlock, const N: usize> BitOr for TinyBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits that are set in either `self` or `rhs`.
    fn bitor(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.blocks[i] | rhs.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitOrAssign for TinyBitSet<T, N> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl<T: BitBlock, const N: usize> BitXor for TinyBitSet<T, N> {
    type Output = Self;

    /// Returns a bitset with all bits that are set in exactly one of `self` and `rhs`.
    fn bitxor(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.blocks[i] ^ rhs.blocks[i]).into()
    }
}

impl<T: BitBlock, const N: usize> BitXorAssign for TinyBitSet<T, N> {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl<T: BitBlock, const N: usize> Debug for TinyBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "TinyBitSet([")?;
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

impl<T: BitBlock, const N: usize> Display for TinyBitSet<T, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Binary::fmt(self, f)
    }
}

impl<T: BitBlock, const N: usize> Binary for TinyBitSet<T, N> {
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

impl<T: BitBlock, const N: usize> LowerHex for TinyBitSet<T, N> {
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

impl<T: BitBlock, const N: usize> UpperHex for TinyBitSet<T, N> {
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
    type TestBitSet = TinyBitSet<u8, 2>;

    #[test]
    fn capacity() {
        fn test_both<T: BitBlock, const N: usize>(expected: usize) {
            assert_eq!(expected, TinyBitSet::<T, N>::CAPACITY);
            assert_eq!(expected, TinyBitSet::<T, N>::default().capacity());
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
    fn new() {
        assert_eq!(TestBitSet::EMPTY, TestBitSet::new());
    }

    #[test]
    fn singleton() {
        let singleton0 = TestBitSet::singleton(0);
        assert!(singleton0[0]);
        assert!(!singleton0[1]);
        assert_eq!(TestBitSet::from([0b0000_0001, 0b0000_0000]), singleton0);
        assert_eq!(
            TestBitSet::from([0b0000_0000, 0b0000_0100]),
            TestBitSet::singleton(10)
        );
    }

    #[test]
    #[should_panic]
    fn singleton_out_of_range() {
        let _ = TestBitSet::singleton(16);
    }

    #[test]
    fn len() {
        assert_eq!(0, TestBitSet::EMPTY.len());
        assert_eq!(1, TestBitSet::singleton(5).len());
        assert_eq!(6, TestBitSet::from([0b1000_0001, 0b0011_1100]).len());
    }

    #[test]
    fn is_empty() {
        assert!(TestBitSet::EMPTY.is_empty());
        assert!(!TestBitSet::singleton(5).is_empty());
        assert!(!TestBitSet::from([0b1000_0001, 0b0011_1100]).is_empty());
        assert!(TestBitSet::from([0b0000_0000, 0b0000_0000]).is_empty());
    }

    #[test]
    fn insert() {
        let mut bs = TestBitSet::EMPTY;
        bs.insert(7);
        assert_eq!(TestBitSet::from([0b1000_0000, 0b0000_0000]), bs);
        bs.insert(10);
        assert_eq!(TestBitSet::from([0b1000_0000, 0b0000_0100]), bs);
        bs.insert(7);
        assert_eq!(TestBitSet::from([0b1000_0000, 0b0000_0100]), bs);
    }

    #[test]
    #[should_panic]
    fn insert_out_of_range() {
        TestBitSet::new().insert(16);
    }

    #[test]
    fn inserted() {
        let bs = TestBitSet::new().inserted(4).inserted(2);
        assert_eq!(TestBitSet::from([0b0001_0100, 0b0000_0000]), bs);
        assert_eq!(bs, bs.inserted(2));
        assert_eq!(bs, bs.inserted(4));
    }

    #[test]
    #[should_panic]
    fn inserted_out_of_range() {
        let _ = TestBitSet::new().inserted(16);
    }

    #[test]
    fn remove() {
        let mut bs = TestBitSet::ALL;
        bs.remove(4);
        assert_eq!(TestBitSet::from([0b1110_1111, 0b1111_1111]), bs);
        bs.remove(2);
        assert_eq!(TestBitSet::from([0b1110_1011, 0b1111_1111]), bs);
        bs.remove(2);
        assert_eq!(TestBitSet::from([0b1110_1011, 0b1111_1111]), bs);
    }

    #[test]
    #[should_panic]
    fn remove_out_of_range() {
        TestBitSet::new().remove(16);
    }

    #[test]
    fn removed() {
        let bs = TestBitSet::singleton(15).inserted(1);
        assert_eq!(TestBitSet::singleton(15), bs.removed(1));
        assert_eq!(TestBitSet::singleton(1), bs.removed(15));
        assert_eq!(bs, bs.removed(2));
        assert_eq!(TestBitSet::EMPTY, bs.removed(1).removed(15));
    }

    #[test]
    #[should_panic]
    fn removed_out_of_range() {
        let _ = TestBitSet::new().removed(16);
    }

    #[test]
    fn toggle() {
        let mut bs = TestBitSet::EMPTY;
        bs.toggle(9);
        assert_eq!(TestBitSet::from([0b0000_0000, 0b0000_0010]), bs);
        bs.toggle(5);
        assert_eq!(TestBitSet::from([0b0010_0000, 0b0000_0010]), bs);
        bs.toggle(5);
        assert_eq!(TestBitSet::from([0b0000_0000, 0b0000_0010]), bs);
    }

    #[test]
    #[should_panic]
    fn toggle_out_of_range() {
        TestBitSet::new().toggle(16);
    }

    #[test]
    fn toggled() {
        let bs = TestBitSet::singleton(11);
        assert_eq!(TestBitSet::EMPTY, bs.toggled(11));
        assert_eq!(bs, bs.toggled(11).toggled(11));
        assert_eq!(bs.inserted(5), bs.toggled(5));
    }

    #[test]
    #[should_panic]
    fn toggled_out_of_range() {
        let _ = TestBitSet::new().toggled(16);
    }

    #[test]
    fn assign() {
        let mut bs = TestBitSet::EMPTY;
        bs.assign(11, true);
        assert_eq!(TestBitSet::from([0b0000_0000, 0b0000_1000]), bs);
        bs.assign(11, true);
        assert_eq!(TestBitSet::from([0b0000_0000, 0b0000_1000]), bs);
        bs.assign(11, false);
        assert_eq!(TestBitSet::EMPTY, bs);
        bs.assign(11, false);
        assert_eq!(TestBitSet::EMPTY, bs);
    }

    #[test]
    #[should_panic]
    fn assign_out_of_range() {
        TestBitSet::new().assign(16, true);
    }

    #[test]
    fn assigned() {
        let bs = TestBitSet::singleton(12);
        assert_eq!(TestBitSet::EMPTY, bs.assigned(12, false));
        assert_eq!(bs, bs.assigned(12, true));
        assert_eq!(bs, bs.assigned(11, false));
        assert_eq!(bs.inserted(11), bs.assigned(11, true));
    }

    #[test]
    #[should_panic]
    fn assigned_out_of_range() {
        let _ = TestBitSet::new().assigned(16, true);
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
            T: Debug + BitBlock + From<TinyBitSet<T, 1>>,
        {
            assert_eq!(x, TinyBitSet::from(x).into());
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
    fn index() {
        let bs = TestBitSet::from([0b1010_1010, 0b0101_0101]);
        assert!(!bs[0]);
        assert!(bs[1]);
        assert!(bs[8]);
        assert!(!bs[9]);
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
            "TinyBitSet([0b00000000, 0b00000000])",
            format!("{:?}", TestBitSet::EMPTY)
        );
        assert_eq!(
            "TinyBitSet([0b11111111, 0b11111111])",
            format!("{:?}", TestBitSet::ALL)
        );
        assert_eq!(
            "TinyBitSet([0b01010101, 0b10101010])",
            format!("{:?}", TestBitSet::from([0b0101_0101, 0b1010_1010]))
        );

        assert_eq!(
            "TinyBitSet([0b00111100])",
            format!("{:#?}", TinyBitSet::from(0b0011_1100_u8))
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
