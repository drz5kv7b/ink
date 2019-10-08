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

use crate::{
    storage::{
        alloc::{
            AllocateUsing,
            BumpAlloc,
            Initialize,
        },
        Key,
        BinaryHeap,
    },
    test_utils::run_test,
};
use crate::storage::collections::binary_heap::impls::HeapType;

fn empty_heap(heap_type: HeapType) -> BinaryHeap<i32> {
    unsafe {
        let mut alloc = BumpAlloc::from_raw_parts(Key([0x0; 32]));
        BinaryHeap::allocate_using(&mut alloc).initialize_into(heap_type)
    }
}

fn filled_heap(heap_type: HeapType) -> BinaryHeap<i32> {
    let mut heap = empty_heap(heap_type);
    heap.push(42);
    heap.push(5);
    heap.push(1337);
    heap.push(77);
    assert_eq!(heap.len(), 4);
    heap
}

/// Pushes all element from `vec` onto the heap, in the order in which they
/// are supplied in the vector.
///
/// Subsequently all elements are popped from the vec and for the retrieved
/// elements it is asserted that they are in the exact same order as the ones
/// in `expected`. The `expected` vec must contain all elements which are
/// returned, as the function finally checks that there are no more elements
/// left in the heap.
fn assert_push_equals_sorted_pop(heap: &mut BinaryHeap<i32>, vec: Vec<i32>, expected: Vec<i32>) {
    vec
        .into_iter()
        .for_each(|i| heap.push(i));

    expected
        .into_iter()
        .for_each(|i| assert_eq!(heap.pop(), Some(i)));

    assert_eq!(heap.pop(), None);
    assert_eq!(heap.len(), 0);
}

#[test]
fn new_unchecked() {
    run_test(|| {
        let heap = empty_heap(HeapType::MIN);
        // Initial invariant.
        assert_eq!(heap.len(), 0);
        assert!(heap.is_empty());
        assert_eq!(heap.iter().next(), None);
    })
}

#[test]
fn put_empty_1() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        // Before and after first put.
        assert_eq!(heap.pop(), None);
        heap.push(42);
        assert_eq!(heap.len(), 1);
        assert_eq!(heap.pop(), Some(42));
    })
}

#[test]
fn put_empty_3() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        // Before and after first put.
        heap.push(10);
        heap.push(20);
        heap.push(10);
        heap.push(20);
        assert_eq!(heap.len(), 4);
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), Some(20));
        assert_eq!(heap.pop(), Some(20));
    })
}

#[test]
fn put_empty_2() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        // Before and after first put.
        assert_eq!(heap.peek(), None);
        heap.push(42);
        assert_eq!(heap.peek(), Some(&42));
    })
}

#[test]
fn put_filled_min() {
    run_test(|| {
        let mut heap = filled_heap(HeapType::MIN);
        // Before and next put.
        // must be ordered
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), Some(42));
        assert_eq!(heap.pop(), Some(77));
        assert_eq!(heap.pop(), Some(1337));
        assert_eq!(heap.pop(), None);
        assert_eq!(heap.len(), 0);
        // Now put.
        heap.push(123);
        assert_eq!(heap.pop(), Some(123));
        assert_eq!(heap.len(), 0);
    })
}

#[test]
fn put_filled_max() {
    run_test(|| {
        let mut heap = filled_heap(HeapType::MAX);
        // Before and next put.
        // must be ordered
        assert_eq!(heap.pop(), Some(1337));
        assert_eq!(heap.pop(), Some(77));
        assert_eq!(heap.pop(), Some(42));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.pop(), None);
        assert_eq!(heap.len(), 0);
        // Now put.
        heap.push(123);
        assert_eq!(heap.pop(), Some(123));
        assert_eq!(heap.len(), 0);
    })
}

#[test]
fn take_empty() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        assert_eq!(heap.pop(), None);
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.peek_mut(), None);
    })
}

#[test]
fn put_empty_4() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        // Before and after first put.
        assert_eq!(heap.pop(), None);
        heap.push(-1);
        heap.push(0);
        heap.push(1);
        assert_eq!(heap.len(), 3);
        assert_eq!(heap.pop(), Some(-1));
        assert_eq!(heap.pop(), Some(0));
        assert_eq!(heap.pop(), Some(1));
    })
}

#[test]
fn put_take() {
    run_test(|| {
        let mut heap = filled_heap(HeapType::MIN);
        assert_eq!(heap.pop(), Some(5));
        heap.push(5);
        assert_eq!(heap.pop(), Some(5));
    })
}

#[test]
fn iter_1() {
    run_test(|| {
        let heap = filled_heap(HeapType::MIN);
        let mut iter = heap.iter();
        assert_eq!(iter.next(), Some((0, &5)));
        assert_eq!(iter.next(), Some((1, &42)));
        assert_eq!(iter.next(), Some((2, &1337)));
        assert_eq!(iter.next(), Some((3, &77)));
        assert_eq!(iter.next(), None);
    })
}

#[test]
fn iter_back() {
    run_test(|| {
        let heap = filled_heap(HeapType::MIN);
        let mut iter = heap.iter();
        assert_eq!(iter.next_back(), Some((3, &77)));
        assert_eq!(iter.next_back(), Some((2, &1337)));
        assert_eq!(iter.next_back(), Some((1, &42)));
        assert_eq!(iter.next_back(), Some((0, &5)));
        assert_eq!(iter.next_back(), None);
    })
}

#[test]
fn iter_size_hint() {
    run_test(|| {
        let heap = filled_heap(HeapType::MIN);
        let mut iter = heap.iter();
        assert_eq!(iter.size_hint(), (4, Some(4)));
        iter.next();
        assert_eq!(iter.size_hint(), (3, Some(3)));
    })
}


#[test]
fn iter_7() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        let vec = vec![5, 42, 1337, 77];
        let mut expected = vec.clone();
        expected.sort();
        assert_push_equals_sorted_pop(&mut heap, vec, expected);
    })
}

#[test]
fn iter_81() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        let vec = vec![20, 40, 30, 10, 29, 21, 40, 31, 22];
        let mut expected = vec.clone();
        expected.sort();
        assert_push_equals_sorted_pop(&mut heap, vec, expected);
    })
}

#[test]
fn iter_8() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MIN);
        let vec = vec![20, 40, 30, 10, 29, 21, 40, 31, 22];
        let mut expected = vec.clone();
        expected.sort();
        assert_push_equals_sorted_pop(&mut heap, vec, expected);
    })
}

#[test]
fn iter_9() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MAX);
        let vec = vec![20, 10, 40, 30, 22, 21, 40, 31, 29];
        let mut expected = vec.clone();
        expected.sort_by(|a, b| b.cmp(a));
        assert_push_equals_sorted_pop(&mut heap, vec, expected);
    })
}

#[test]
fn iter_11() {
    run_test(|| {
        let mut heap = empty_heap(HeapType::MAX);
        let vec = vec![20, 10, 40, 30, 21];
        let mut expected = vec.clone();
        expected.sort_by(|a, b| b.cmp(a));
        assert_push_equals_sorted_pop(&mut heap, vec, expected);
    })
}
