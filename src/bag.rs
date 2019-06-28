//! Data structures for storing and reclaiming retired records.

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

use core::mem;

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
        debug_assert!(bag.is_empty());
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
        Self { queues: [BagQueue::new(), BagQueue::new(), BagQueue::new()], curr_idx: 0 }
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
///
/// # Note
///
/// A [`BagQueue`] must never be dropped when there are still un-reclaimed
/// retired records in any of its [`BagNode`]s.
#[derive(Debug)]
pub struct BagQueue<R: Reclaim + 'static> {
    head: Box<BagNode<R>>,
}

impl<R: Reclaim + 'static> BagQueue<R> {
    /// Consumes `self`, returning the internal head [`BagNode`], it is
    /// non-empty, otherwise returning [`None`] and dropping the [`BagQueue`].
    #[inline]
    pub fn into_non_empty(self) -> Option<Box<BagNode<R>>> {
        if !self.is_empty() {
            Some(self.head)
        } else {
            None
        }
    }

    /// Creates a new [`BagQueue`].
    #[inline]
    fn new() -> Self {
        Self { head: BagNode::boxed() }
    }

    /// Returns `true` if the head node is both empty and has no successor.
    #[inline]
    fn is_empty(&self) -> bool {
        self.head.is_empty()
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
            bag.reclaim_all();
            node = bag.next.take();
            bag_pool.recycle_bag(bag);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// BagNode
////////////////////////////////////////////////////////////////////////////////////////////////////

const DEFAULT_BAG_SIZE: usize = 256;

/// A linked list node containing an inline vector for storing retired records.
#[derive(Debug)]
pub struct BagNode<R: Reclaim + 'static> {
    next: Option<Box<BagNode<R>>>,
    retired_records: ArrayVec<[Retired<R>; DEFAULT_BAG_SIZE]>,
}

impl<R: Reclaim> BagNode<R> {
    /// Reclaims all retired records in this [`BagNode`].
    ///
    /// # Safety
    ///
    /// It must be ensured that the contents of the queue are at least two
    /// epochs old.
    #[inline]
    pub unsafe fn reclaim_all(&mut self) {
        self.reclaim_inner();

        let mut curr = self.next.take();
        while let Some(mut node) = curr {
            node.reclaim_inner();
            curr = node.next.take();
        }
    }

    /// Creates a new boxed [`BagNode`].
    #[inline]
    fn boxed() -> Box<Self> {
        Box::new(Self { next: None, retired_records: ArrayVec::default() })
    }

    /// Returns `true` if the [`BagNode`] is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.next.is_none() && self.retired_records.len() == 0
    }

    #[inline]
    unsafe fn reclaim_inner(&mut self) {
        for mut record in self.retired_records.drain(..) {
            record.reclaim();
        }
    }
}

impl<R: Reclaim + 'static> Drop for BagNode<R> {
    #[inline]
    fn drop(&mut self) {
        // unproblematic, as bag nodes are rarely dropped
        assert!(self.is_empty(), "`BagNode`s must not be dropped unless empty (would leak memory)");
    }
}

#[cfg(test)]
mod tests {
    use std::ptr::NonNull;

    use reclaim::leak::Leaking;

    use super::{BAG_QUEUE_COUNT, DEFAULT_BAG_SIZE};
    use crate::epoch::PossibleAge;

    type EpochBagQueues = super::EpochBagQueues<Leaking>;
    type BagPool = super::BagPool<Leaking>;
    type BagQueue = super::BagQueue<Leaking>;
    type Retired = reclaim::Retired<Leaking>;

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // BagQueue tests
    ////////////////////////////////////////////////////////////////////////////////////////////////

    /// A factory for dummy retired records.
    fn retired() -> Retired {
        let ptr: NonNull<()> = NonNull::dangling();
        unsafe { Retired::new_unchecked(ptr) }
    }

    #[test]
    fn empty_bag_queue() {
        let bag_queue = BagQueue::new();
        assert!(bag_queue.is_empty());
        assert!(bag_queue.into_non_empty().is_none());
    }

    #[test]
    fn non_empty_bag_queue() {
        let mut pool = BagPool::new();

        let mut bag_queue = BagQueue::new();
        for _ in 0..DEFAULT_BAG_SIZE - 1 {
            bag_queue.retire_record(retired(), &mut pool);
        }

        // head is almost full and is the only node
        assert!(!bag_queue.is_empty());
        assert!(bag_queue.head.next.is_none());

        bag_queue.retire_record(retired(), &mut pool);
        // head node is empty but has a `next` node (the previous head)
        assert_eq!(bag_queue.head.retired_records.len(), 0);
        assert!(bag_queue.head.next.is_some());
        assert!(!bag_queue.is_empty());

        let mut node = bag_queue.into_non_empty().unwrap();
        // bag queues must never be dropped when there are still retired records
        // in them (would be a memory leak)
        unsafe { node.reclaim_all() };
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // EpochBagQueues tests
    ////////////////////////////////////////////////////////////////////////////////////////////////

    #[test]
    fn rotate_and_reclaim() {
        let mut pool = BagPool::new();

        let mut bags = EpochBagQueues::new();
        // insert one bag worth of records + one record (allocates a new node)
        for _ in 0..=DEFAULT_BAG_SIZE {
            bags.retire_record(retired(), &mut pool);
        }

        unsafe { bags.rotate_and_reclaim(&mut pool) };
        unsafe { bags.rotate_and_reclaim(&mut pool) };
        // upon completing the cycle, one full bag is reclaimed and returned to
        // pool, one retired record remains in the old bag.
        unsafe { bags.rotate_and_reclaim(&mut pool) };

        assert_eq!(pool.0.len(), 1);
        assert_eq!(bags.queues[0].head.retired_records.len(), 1);

        unsafe { bags.queues[0].head.reclaim_all() };
    }

    #[test]
    fn retire_by_age() {
        let mut pool = BagPool::new();

        // insert enough records so that the head node in all three epoch bags
        // is one record away from being full, so no full bags are reclaimed on
        // rotation
        let mut bags = EpochBagQueues::new();
        for _ in 0..BAG_QUEUE_COUNT {
            for _ in 0..DEFAULT_BAG_SIZE - 1 {
                bags.retire_record(retired(), &mut pool);
                unsafe { bags.rotate_and_reclaim(&mut pool) };
            }
        }
        // this is inserted into the currently oldest bag queue at index 1
        bags.retire_record_by_age(retired(), PossibleAge::TwoEpochs, &mut pool);
        assert_eq!(bags.curr_idx, 0);
        assert_eq!(bags.queues[1].head.retired_records.len(), 0);
        assert!(bags.queues[1].head.next.is_some());

        // rotates the epoch bags to index 1 and reclaims one full bag there
        unsafe { bags.rotate_and_reclaim(&mut pool) };
        assert_eq!(pool.0.len(), 1);

        // this is inserted into the previous bag queue at index 0
        bags.retire_record_by_age(retired(), PossibleAge::OneEpoch, &mut pool);
        assert_eq!(bags.curr_idx, 1);
        assert_eq!(bags.queues[0].head.retired_records.len(), 0);
        assert!(bags.queues[0].head.next.is_some());

        // rotates the epoch bags to index 2
        unsafe { bags.rotate_and_reclaim(&mut pool) };

        // this is inserted into the current bag queue at index 2
        bags.retire_record_by_age(retired(), PossibleAge::SameEpoch, &mut pool);
        assert_eq!(bags.curr_idx, 2);
        // one bag has been re-allocated from the pool
        assert_eq!(pool.0.len(), 0);
        assert_eq!(bags.queues[2].head.retired_records.len(), 0);
        assert!(bags.queues[2].head.next.is_some());

        // rotates the epoch bags to index 0 and reclaims one full bag there
        unsafe { bags.rotate_and_reclaim(&mut pool) };
        assert_eq!(bags.curr_idx, 0);
        assert_eq!(pool.0.len(), 1);
        unsafe { bags.rotate_and_reclaim(&mut pool) };
        assert_eq!(bags.curr_idx, 1);
        // rotates the epoch bags to index 2 and reclaims one full bag there
        unsafe { bags.rotate_and_reclaim(&mut pool) };
        assert_eq!(bags.curr_idx, 2);
        assert_eq!(pool.0.len(), 2);

        // all epoch queues are empty again
    }
}
