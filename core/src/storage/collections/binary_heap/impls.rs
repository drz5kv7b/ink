// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of ink!.
//
// ink! is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ink! is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ink!.  If not, see <http://www.gnu.org/licenses/>.

use crate::storage::{
    self,
    alloc::{
        Allocate,
        AllocateUsing,
        Initialize,
    },
    chunk::SyncChunk,
    Flush,
};
use core::cmp;
#[cfg(feature = "ink-generate-abi")]
use ink_abi::{
    HasLayout,
    LayoutField,
    LayoutStruct,
    StorageLayout,
};
use scale::{
    Decode,
    Encode,
};
#[cfg(feature = "ink-generate-abi")]
use type_metadata::Metadata;

/// We implement a ternary tree, i.e. a k-ary tree with k = 3
const CHILDS: u32 = 3;

/// A ternary heap collection.
///
/// Provides `O(log(n))` push and pop operations.
#[derive(Debug)]
#[cfg_attr(feature = "ink-generate-abi", derive(Metadata))]
pub struct BinaryHeap<T> {
    /// Stores densely packed general stash information.
    header: storage::Value<BinaryHeapHeader>,
    /// The entries of the stash.
    entries: SyncChunk<T>,
}

#[derive(Debug, Encode, Decode)]
pub enum HeapType {
    /// A min-heap, a nodes value is smaller than or equal to the values in its children.
    MIN,
    /// A max-heap, a nodes value is greater than or equal to the values in its children.
    MAX
}

/// Densely stored general information required by a stash.
///
/// # Note
///
/// Separation of these fields into a sub structure has been made
/// for performance reasons so that they all reside in the same
/// storage entity. This allows implementations to perform less reads
/// and writes to the underlying contract storage.
#[derive(Debug, Encode, Decode)]
#[cfg_attr(feature = "ink-generate-abi", derive(Metadata))]
struct BinaryHeapHeader {
    /// The number of items stored in the stash.
    len: u32,
    /// The heap type, min or max.
    heap_type: HeapType,
}

impl Flush for BinaryHeapHeader {
    fn flush(&mut self) {
        self.len.flush();
    }
}

/// Iterator over the values of a stash.
#[derive(Debug)]
pub struct Values<'a, T> {
    /// The underlying iterator.
    iter: Iter<'a, T>,
}

impl<'a, T> Values<'a, T> {
    /// Creates a new iterator for the given storage stash.
    pub(crate) fn new(heap: &'a BinaryHeap<T>) -> Self
    where
        T: scale::Codec + cmp::PartialOrd,
    {
        Self { iter: heap.iter() }
    }
}

impl<T> Flush for BinaryHeap<T>
where
    T: Encode + Flush,
{
    fn flush(&mut self) {
        self.header.flush();
        self.entries.flush();
    }
}

#[cfg(feature = "ink-generate-abi")]
impl<T> HasLayout for BinaryHeap<T>
where
    T: Metadata + 'static,
{
    fn layout(&self) -> StorageLayout {
        LayoutStruct::new(
            Self::meta_type(),
            vec![
                LayoutField::of("header", &self.header),
                LayoutField::of("entries", &self.entries),
            ],
        )
        .into()
    }
}

impl<'a, T> Iterator for Values<'a, T>
where
    T: scale::Codec + cmp::PartialOrd,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(_index, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, T> ExactSizeIterator for Values<'a, T>
where
    T: scale::Codec + cmp::PartialOrd,
{}

impl<'a, T> DoubleEndedIterator for Values<'a, T>
where
    T: scale::Codec + cmp::PartialOrd,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(_index, value)| value)
    }
}

/// Unordered iterator over the elements of a heap.
#[derive(Debug)]
pub struct Iter<'a, T> {
    /// The heap that is iterated over.
    heap: &'a BinaryHeap<T>,
    /// The index of the current start item of the iteration.
    begin: u32,
    /// The index of the current end item of the iteration.
    end: u32,
    /// The amount of already yielded items.
    ///
    /// Required to offer an exact `size_hint` implementation.
    /// Also can be used to exit iteration as early as possible.
    yielded: u32,
}

impl<'a, T> Iter<'a, T> {
    /// Creates a new iterator for the given storage stash.
    pub(crate) fn new(heap: &'a BinaryHeap<T>) -> Self
    where
        T: scale::Codec + cmp::PartialOrd,
    {
        Self {
            heap,
            begin: 0,
            end: heap.len(),
            yielded: 0,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T>
where
    T: scale::Codec + cmp::PartialOrd,
{
    type Item = (u32, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.begin <= self.end);
        if self.yielded == self.heap.len() {
            return None
        }
        while self.begin < self.end {
            let cur = self.begin;
            self.begin += 1;
            if let Some(elem) = self.heap.get(cur) {
                self.yielded += 1;
                return Some((cur, elem))
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.heap.len() - self.yielded) as usize;
        (remaining, Some(remaining))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T>
where
    T: scale::Codec + cmp::PartialOrd,
{}

impl<'a, T> DoubleEndedIterator for Iter<'a, T>
where
    T: scale::Codec + cmp::PartialOrd,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        debug_assert!(self.begin <= self.end);
        if self.yielded == self.heap.len() {
            return None
        }
        while self.begin < self.end {
            self.end -= 1;
            if let Some(elem) = self.heap.get(self.end) {
                self.yielded += 1;
                return Some((self.end, elem))
            }
        }
        None
    }
}

impl<T> Encode for BinaryHeap<T> {
    fn encode_to<W: scale::Output>(&self, dest: &mut W) {
        self.header.encode_to(dest);
        self.entries.encode_to(dest);
    }
}

impl<T> Decode for BinaryHeap<T> {
    fn decode<I: scale::Input>(input: &mut I) -> Result<Self, scale::Error> {
        let header = storage::Value::decode(input)?;
        let entries = SyncChunk::decode(input)?;
        Ok(Self { header, entries })
    }
}

impl<T> AllocateUsing for BinaryHeap<T> {
    unsafe fn allocate_using<A>(alloc: &mut A) -> Self
    where
        A: Allocate,
    {
        Self {
            header: storage::Value::allocate_using(alloc),
            entries: SyncChunk::allocate_using(alloc),
        }
    }
}

impl<T> Initialize for BinaryHeap<T> {
    type Args = HeapType;

    fn default_value() -> Option<Self::Args> {
        Some(HeapType::MIN)
    }

    fn initialize(&mut self, heap_type: Self::Args) {
        self.header.set(BinaryHeapHeader {
            len: 0,
            heap_type: heap_type,
        });
    }
}

impl<T> BinaryHeap<T>
where
    T: scale::Codec + cmp::PartialOrd,
{
    /// Returns the element stored at index `n` if any.
    pub fn len(&self) -> u32 {
        self.header.len
    }

    /// Returns `true` if the heap is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the greatest item if not empty.
    pub fn peek(&self) -> Option<&T> {
        self.get(0)
    }

    /// Mutates the greatest item if not empty and returns a reference to the result.
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.entries.get_mut(0)
    }

    /// Removes the top item from the heap if not empty.
    ///
    /// Complexity is `O(log(n))`.
    pub fn pop(&mut self) -> Option<T> {
        if self.header.len == 0 {
            return None;
        }

        let tmp = self.entries.take(0);
        if self.header.len == 1 {
            self.header.len -= 1;
            return tmp;
        }

        self.relocate(self.header.len - 1, 0);

        self.header.len -= 1;
        self.repair_top();
        tmp
    }

    /// Move the top of the heap to its correct place within the heap, so that
    /// sort order is maintained.
    fn repair_top(&mut self) {
        let mut top_index = 0;
        let top_value = self.entries.take(top_index)
            .expect("failed taking top element from heap");
        let mut succ_index = self.find_successor(
            top_index * CHILDS + 1,
            top_index * CHILDS + CHILDS
        );
        while succ_index < self.header.len && {
            let succ_value = self.entries.get(succ_index)
                .expect("failed retrieving successor");
            match self.header.heap_type {
                HeapType::MIN => top_value > *succ_value,
                HeapType::MAX => top_value < *succ_value,
            }
        } {
            self.relocate(succ_index, top_index);
            top_index = succ_index;
            succ_index = self.find_successor(
                succ_index * CHILDS + 1,
                succ_index * CHILDS + CHILDS
            );
        }
        let _ = self.entries.put(top_index, top_value);
    }

    ///  Returns the child node with
    ///     * in case of `HeapType::MIN` the lowest value.
    ///     * in case of `HeapType::MAX` the largest value.
    ///
    /// The `from` parameter refers to the start index of the search,
    /// the `to` parameter to the end index for the search.
    fn find_successor(&mut self, from: u32, to: u32) -> u32 {
        let mut succ_index = from;
        let mut i = from + 1;

        while i <= to && i < self.header.len {
            let succ_value = self.get(succ_index)
                .expect("failed getting successor value");
            let i_value = self.get(i)
                .expect("failed getting value at index");
            let is_successor = match self.header.heap_type {
                HeapType::MIN => succ_value > i_value,
                HeapType::MAX => succ_value < i_value,
            };
            if is_successor {
                succ_index = i;
            }
            i += 1;
        }
        succ_index
    }

    /// Returns the first item if not empty.
    ///
    /// In case of `HeapType::MIN` this is the smallest item, in case of
    /// `HeapType::MAX` the largest.
    fn get(&self, n: u32) -> Option<&T> {
        self.entries.get(n)
    }

    /// Pushes an item onto the heap.
    ///
    /// Panics in case the heap already contains `u32::MAX` items.
    /// Complexity is `O(log(n))`.
    pub fn push(&mut self, val: T) {
        if self.len() == u32::max_value() {
            panic!(
                "[ink_core::Vec::push] Error: \
                 cannot push more elements than `u32::MAX`"
            )
        }

        // TODO this parapgraph
        self.header.len += 1;
        let mut index = self.header.len - 1;
        let mut parent_index = {
            if index > 0 {
                self.parent_index(index)
            } else {
                0
            }
        };

        // Relocate until the item is smaller (`HeapType::MIN`) or greater (`HeapType::MAX`)
        // than its parent value.
        while index != 0 && {
            let parent_value = self.get(parent_index)
                .expect("failed getting parent value");
            match self.header.heap_type {
                HeapType::MIN => val < *parent_value,
                HeapType::MAX => val > *parent_value,
            }
        } {
            self.relocate(parent_index, index);

            index = parent_index;
            if index > 0 {
                parent_index = self.parent_index(index);
            }
        }
        let _ = self.entries.put(index, val);
    }

    /// Returns an iterator over the references of all values of the stash.
    ///
    /// # Note
    ///
    /// - It is **not** recommended to iterate over all elements of a storage stash.
    /// - Try to avoid this if possible or iterate only over a minimal subset of
    ///   all elements using e.g. `Iterator::take(n)`.
    pub fn values(&self) -> Values<T> {
        Values::new(self)
    }

    fn relocate(&mut self, from: u32, to: u32) {
        let entry = self.entries.take(from)
            .expect("failed relocating item");
        let _ = self.entries.put(to, entry);
    }

    fn parent_index(&self, n: u32) -> u32 {
        (n - 1) / CHILDS
    }

    /// Returns an unordered iterator over all items of the heap.
    ///
    /// # Note
    ///
    /// - The iteration is not guaranteed to be ordered!
    /// - It is **not** recommended to iterate over all elements of a storage stash.
    /// - Try to avoid this if possible or iterate only over a minimal subset of
    ///   all elements using e.g. `Iterator::take(n)`.
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }
}
