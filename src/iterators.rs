use std::iter::FusedIterator;

use crate::BitBlock;

/// Iterator over the set bits in a bitset.
///
/// Yields the indices of the set bits in ascending order.
#[derive(Debug, Clone)]
pub struct IntoIter<T: BitBlock, const N: usize> {
    blocks: [T; N],
    index_front: usize,
    index_back: usize,
}

impl<T: BitBlock, const N: usize> IntoIter<T, N> {
    pub(crate) fn new(blocks: [T; N]) -> Self {
        Self {
            blocks,
            index_front: 0,
            index_back: N - 1,
        }
    }
}

impl<T: BitBlock, const N: usize> Iterator for IntoIter<T, N> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.index_front <= self.index_back {
            let block = &mut self.blocks[self.index_front];
            if *block == T::EMPTY {
                self.index_front += 1;
                continue;
            }

            let idx_in_block = block.trailing_zeros() as usize;
            *block ^= T::LSB << idx_in_block;
            return Some(idx_in_block + self.index_front * T::BITS);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(N * T::BITS))
    }
}

impl<T: BitBlock, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while self.index_front <= self.index_back {
            let block = &mut self.blocks[self.index_back];
            if *block == T::EMPTY {
                let Some(new_index_back) = self.index_back.checked_sub(1) else {
                    break;
                };
                self.index_back = new_index_back;
                continue;
            }

            let idx_in_block = T::BITS - 1 - block.leading_zeros() as usize;
            *block ^= T::LSB << idx_in_block;
            return Some(idx_in_block + self.index_back * T::BITS);
        }

        None
    }
}

impl<T: BitBlock, const N: usize> FusedIterator for IntoIter<T, N> {}

#[cfg(test)]
mod tests {
    use super::*;

    /// Iterator type for most tests
    type TestIter = IntoIter<u8, 2>;

    #[test]
    fn forward_iteration() {
        let iter = TestIter::new([0b1000_1001, 0b1000_0100]);
        let expected = vec![0, 3, 7, 10, 15];
        assert_eq!(expected, iter.collect::<Vec<_>>());
    }

    #[test]
    fn backward_iteration() {
        let iter = TestIter::new([0b0100_0100, 0b0110_0001]);
        let expected = vec![14, 13, 8, 6, 2];
        assert_eq!(expected, iter.rev().collect::<Vec<_>>());
    }

    #[test]
    fn mixed_forward_backward_iteration() {
        let mut iter = TestIter::new([0b0100_0000, 0b0110_0001]);
        assert_eq!(Some(14), iter.next_back());
        assert_eq!(Some(6), iter.next());
        assert_eq!(Some(8), iter.next());
        assert_eq!(Some(13), iter.next_back());
    }
}
