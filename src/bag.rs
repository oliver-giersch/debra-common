//! Data structures for storing and reclaiming retired records.

use core::mem;

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

use arrayvec::ArrayVec;
use reclaim::{Reclaim, Retired};

use crate::epoch::PossibleAge;

////////////////////////////////////////////////////////////////////////////////////////////////////
// BagPool
////////////////////////////////////////////////////////////////////////////////////////////////////

const BAG_POOL_SIZE: usize = 16;

/// A pool for storing and recycling no longer used [`BagNode`]s of a thread.
#[derive(Debug)]
pub struct BagPool<R: Reclaim + 'static>(ArrayVec<[Box<BagNode<R>>; BAG_POOL_SIZE]>);

impl<R: Reclaim + 'static> Default for BagPool<R> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<R: Reclaim + 'static> BagPool<R> {
    /// Creates a new (empty) [`BagPool`].
    #[inline]
    pub fn new() -> Self {
        Self(ArrayVec::default())
    }

    /// Creates a new [`BagPool`] with the maximum number of pre-allocated bags.
    #[inline]
    pub fn with_bags() -> Self {
        Self((0..BAG_POOL_SIZE).map(|_| BagNode::boxed()).collect())
    }

    /// Allocates a new [`BagNode`] from the pool or from the global allocator,
    /// if the pools is currently empty.
    #[inline]
    fn allocate_bag(&mut self) -> Box<BagNode<R>> {
        self.0.pop().unwrap_or_else(BagNode::boxed)
    }

    /// Recycles an empty [`BagNode`] back into the pool or deallocates it, if
    /// the pool is currently full.
    #[inline]
    fn recycle_bag(&mut self, bag: Box<BagNode<R>>) {
        debug_assert_eq!(bag.retired_records.len(), 0);
        if let Err(cap) = self.0.try_push(bag) {
            mem::drop(cap.element());
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// BagQueue
////////////////////////////////////////////////////////////////////////////////////////////////////

const BAG_QUEUE_COUNT: usize = 3;

/// A ring buffer with three [`BagQueue`]s
///
/// Each [`BagQueue`] caches the records that were retired in a specific epoch
/// and these are continuously recycled, as the oldest records are reclaimed
/// when the global epoch is advanced.
#[derive(Debug)]
pub struct EpochBagQueues<R: Reclaim + 'static> {
    queues: [BagQueue<R>; BAG_QUEUE_COUNT],
    curr_idx: usize,
}

impl<R: Reclaim + 'static> Default for EpochBagQueues<R> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<R: Reclaim + 'static> EpochBagQueues<R> {
    /// Creates a new set of [`EpochBagQueues`].
    #[inline]
    pub fn new() -> Self {
        Self {
            queues: [BagQueue::new(), BagQueue::new(), BagQueue::new()],
            curr_idx: 0,
        }
    }

    /// Sorts the set of [`BagQueues`] from most recent to oldest and returns
    /// the sorted array with three elements.
    #[inline]
    pub fn into_sorted(self) -> [BagQueue<R>; BAG_QUEUE_COUNT] {
        let [a, b, c] = self.queues;
        match self.curr_idx {
            0 => [a, c, b],
            1 => [b, a, c],
            2 => [c, b, a],
            _ => unreachable!(),
        }
    }

    /// Retires the given `record` in the current [`BagQueue`].
    #[inline]
    pub fn retire_record(&mut self, record: Retired<R>, bag_pool: &mut BagPool<R>) {
        self.retire_record_by_age(record, PossibleAge::SameEpoch, bag_pool);
    }

    /// Retires the given `record` in the appropriate [`BagQueue`] based on the
    /// specified `age`.
    #[inline]
    pub fn retire_record_by_age(
        &mut self,
        record: Retired<R>,
        age: PossibleAge,
        bag_pool: &mut BagPool<R>,
    ) {
        let queue = match age {
            PossibleAge::SameEpoch => &mut self.queues[self.curr_idx],
            PossibleAge::OneEpoch => &mut self.queues[(self.curr_idx + 2) % BAG_QUEUE_COUNT],
            PossibleAge::TwoEpochs => &mut self.queues[(self.curr_idx + 1) % BAG_QUEUE_COUNT],
        };

        queue.retire_record(record, bag_pool);
    }

    /// Retires the given `record` in the current [`BagQueue`] as the final
    /// record of an exiting thread.
    ///
    /// # Safety
    ///
    /// After calling this method, no further calls to `retire_record`,
    /// `retire_record_by_age` or `retire_final_record` must be made.
    #[inline]
    pub unsafe fn retire_final_record(&mut self, record: Retired<R>) {
        let curr = &mut self.queues[self.curr_idx];
        curr.head.retired_records.push_unchecked(record);
    }

    /// Advances the current epoch bag and reclaims all records in the oldest
    /// bag.
    ///
    /// Full bags that are reclaimed during this process are emptied and sent
    /// back into the `bag_pool`.
    ///
    /// # Safety
    ///
    /// It must ensured that two full epochs have actually passed since the
    /// records in the oldest bag have been retired.
    #[inline]
    pub unsafe fn rotate_and_reclaim(&mut self, bag_pool: &mut BagPool<R>) {
        self.curr_idx = (self.curr_idx + 1) % BAG_QUEUE_COUNT;
        self.queues[self.curr_idx].reclaim_full_bags(bag_pool);
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// BagQueue
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A LIFO queue of [`RetiredBag`]s.
///
/// All nodes except the first one are guaranteed to be full and the first one
/// is guaranteed to always have enough space for at least one additional
/// record.
#[derive(Debug)]
pub struct BagQueue<R: Reclaim + 'static> {
    head: Box<BagNode<R>>,
}

impl<R: Reclaim + 'static> BagQueue<R> {
    /// Consumes `self`, returning it again if it is non-empty, otherwise
    /// returning [`None`] and dropping the [`BagQueue`].
    #[inline]
    pub fn into_non_empty(self) -> Option<Self> {
        if !self.is_empty() {
            Some(self)
        } else {
            None
        }
    }

    /// Creates a new [`BagQueue`].
    #[inline]
    fn new() -> Self {
        Self {
            head: BagNode::boxed(),
        }
    }

    /// Returns `true` if the head node is both empty and has no successor.
    #[inline]
    fn is_empty(&self) -> bool {
        self.head.retired_records.len() == 0 && self.head.next.is_none()
    }

    /// Retires the given `record`.
    ///
    /// If the operation requires a new bag to be allocated, it is attempted to
    /// be taken from `bag_pool`.
    #[inline]
    fn retire_record(&mut self, record: Retired<R>, bag_pool: &mut BagPool<R>) {
        // the head bag is guaranteed to never be full
        unsafe { self.head.retired_records.push_unchecked(record) };
        if self.head.retired_records.is_full() {
            let mut old_head = bag_pool.allocate_bag();
            mem::swap(&mut self.head, &mut old_head);
            self.head.next = Some(old_head);
        }
    }

    /// Reclaims all records in all **full** bags.
    ///
    /// # Safety
    ///
    /// It must be ensured that the contents of the queue are at least two
    /// epochs old.
    #[inline]
    unsafe fn reclaim_full_bags(&mut self, bag_pool: &mut BagPool<R>) {
        let mut node = self.head.next.take();
        while let Some(mut bag) = node {
            node = bag.next.take();
            for mut record in bag.retired_records.drain(..) {
                record.reclaim();
            }

            bag_pool.recycle_bag(bag);
        }
    }
}

impl<R: Reclaim + 'static> Drop for BagQueue<R> {
    #[inline]
    fn drop(&mut self) {
        let mut curr = self.head.next.take();
        while let Some(mut node) = curr {
            curr = node.next.take();
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// BagNode
////////////////////////////////////////////////////////////////////////////////////////////////////

const DEFAULT_BAG_SIZE: usize = 256;

#[derive(Debug)]
struct BagNode<R: Reclaim + 'static> {
    next: Option<Box<BagNode<R>>>,
    retired_records: ArrayVec<[Retired<R>; DEFAULT_BAG_SIZE]>,
}

impl<R: Reclaim> BagNode<R> {
    /// Creates a new boxed [`BagNode`].
    #[inline]
    fn boxed() -> Box<Self> {
        Box::new(Self {
            next: None,
            retired_records: ArrayVec::default(),
        })
    }
}
