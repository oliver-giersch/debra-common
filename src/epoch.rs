//! Type-safe epoch counters for tracking operations of threads.

use core::fmt;
use core::ops::{Add, Sub};
use core::sync::atomic::{AtomicUsize, Ordering};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Epoch
////////////////////////////////////////////////////////////////////////////////////////////////////

const EPOCH_INCREMENT: usize = 2;

/// A monotonically increasing epoch counter with wrapping overflow behaviour.
#[derive(Copy, Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Epoch(usize);

impl Epoch {
    /// Creates a new [`Epoch`] starting at zero.
    #[inline]
    pub fn new() -> Self {
        Self(0)
    }

    /// Returns the [`PossibleAge`] of the epoch relative to `global_epoch`.
    ///
    /// Since the global epoch is explicitly allowed to wrap around, it is not
    /// possible to unambiguously determine the relative age of an epoch.
    /// However, since epochs are monotonically increasing it is certain that
    /// any previously observed epoch must be older of equal than the global
    /// epoch.
    /// Consequently, it is possible to determine if an epoch **could** be
    /// within the critical range of two epochs, during which reclamation of
    /// records **must** be avoided, and is in order to be conservative.
    #[inline]
    pub fn relative_age(self, global_epoch: Epoch) -> Result<PossibleAge, Undetermined> {
        match global_epoch.0.wrapping_sub(self.0) {
            0 => Ok(PossibleAge::SameEpoch),
            2 => Ok(PossibleAge::OneEpoch),
            4 => Ok(PossibleAge::TwoEpochs),
            _ => Err(Undetermined),
        }
    }

    #[inline]
    pub(crate) fn with_epoch(epoch: usize) -> Self {
        debug_assert_eq!(epoch % EPOCH_INCREMENT, 0);
        Self(epoch)
    }

    #[inline]
    pub(crate) fn into_inner(self) -> usize {
        self.0
    }
}

impl Add<usize> for Epoch {
    type Output = Self;

    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0.wrapping_add(rhs * EPOCH_INCREMENT))
    }
}

impl Sub<usize> for Epoch {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        Self(self.0.wrapping_sub(rhs * EPOCH_INCREMENT))
    }
}

impl fmt::Display for Epoch {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "epoch {}", self.0 / EPOCH_INCREMENT)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// AtomicEpoch
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A concurrently accessible [`Epoch`].
pub struct AtomicEpoch(AtomicUsize);

impl AtomicEpoch {
    /// Creates a new [`AtomicEpoch`] starting at zero.
    #[inline]
    pub const fn new() -> Self {
        Self(AtomicUsize::new(0))
    }

    /// Loads the [`Epoch`] value.
    ///
    /// `load` takes an [`Ordering`][ordering] argument, which describes the
    /// memory ordering of this operation.
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`][release] or [`AcqRel`][acq_rel].
    ///
    /// [ordering]: core::sync::atomic::Ordering
    /// [release]: core::sync::atomic::Ordering::Release
    /// [acq_rel]: core::sync::atomic::Ordering::AcqRel
    #[inline]
    pub fn load(&self, order: Ordering) -> Epoch {
        Epoch(self.0.load(order))
    }

    /// Stores a value into the [`Epoch`] if the current value is equal to
    /// `current`.
    ///
    /// The return value is always the previous value. If it is equal to
    /// `current`, then the value was updated.
    ///
    /// `compare_and_swap` also takes an [`Ordering`][ordering] argument, which
    /// describes the memory ordering of this operation.
    /// Notice that even when using [`AcqRel`][acq_rel], the operation might
    /// fail and hence just perform an `Acquire` load, but not have `Release`
    /// semantics.
    /// Using [`Acquire`][acquire] makes the store part of this operation
    /// [`Relaxed`][relaxed], if it happens, and using [`Release`][release]
    /// makes the load part [`Relaxed`][relaxed].
    ///
    /// [ordering]: core::sync::atomic::Ordering
    /// [acquire]: core::sync::atomic::Ordering::Acquire
    /// [acq_rel]: core::sync::atomic::Ordering::AcqRel
    /// [relaxed]: core::sync::atomic::Ordering::Relaxed
    /// [release]: core::sync::atomic::Ordering::Release
    #[inline]
    pub fn compare_and_swap(&self, current: Epoch, new: Epoch, order: Ordering) -> Epoch {
        Epoch(self.0.compare_and_swap(current.0, new.0, order))
    }
}

impl fmt::Debug for AtomicEpoch {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("AtomicEpoch").field("epoch", &self.0.load(Ordering::SeqCst)).finish()
    }
}

impl fmt::Display for AtomicEpoch {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "epoch {}", self.0.load(Ordering::SeqCst) / EPOCH_INCREMENT)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// PossibleAge
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The possible age of an epoch in relation to global epoch within a two-epoch
/// range.
///
/// See [`relative_age`][Epoch::relative_age] for more details.
#[derive(Debug, Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum PossibleAge {
    /// Epoch *may* be the same as the global epoch.
    SameEpoch,
    /// Epoch *may* be one epoch older than the global epoch.
    OneEpoch,
    /// Epoch *may* be two epochs older than the global epoch.
    TwoEpochs,
}

impl fmt::Display for PossibleAge {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PossibleAge::SameEpoch => write!(f, "epoch could be the same"),
            PossibleAge::OneEpoch => write!(f, "epoch could be one epoch old"),
            PossibleAge::TwoEpochs => write!(f, "epoch could be two epochs old"),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Undetermined
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A type indicating that the age of an [`Epoch`] can not be determined, but is
/// definitely older than two epochs.
#[derive(Debug, Default, Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct Undetermined;

impl fmt::Display for Undetermined {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "epoch age is undetermined, but older than two epochs")
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering::Relaxed;

    use super::{AtomicEpoch, Epoch, PossibleAge};

    #[test]
    fn new_epoch() {
        let zero = Epoch::new();
        assert_eq!(zero.into_inner(), 0);
        let ten = Epoch::with_epoch(20);
        assert_eq!(ten.into_inner(), 20);
        assert_eq!(zero + 10, ten);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn illegal_epoch() {
        let _epoch = Epoch::with_epoch(11);
    }

    #[test]
    fn relative_age() {
        let zero = Epoch::new();
        assert_eq!(zero.relative_age(zero).unwrap(), PossibleAge::SameEpoch);
        assert_eq!(zero.relative_age(zero + 1).unwrap(), PossibleAge::OneEpoch);
        assert_eq!(zero.relative_age(zero + 2).unwrap(), PossibleAge::TwoEpochs);

        let max = Epoch::with_epoch(std::usize::MAX - 1);
        assert_eq!(max.relative_age(zero).unwrap(), PossibleAge::OneEpoch);
        assert_eq!((max - 1).relative_age(zero).unwrap(), PossibleAge::TwoEpochs);
    }

    #[test]
    fn atomic_epoch() {
        let atomic_epoch = AtomicEpoch::new();
        let epoch = atomic_epoch.load(Relaxed);
        assert_eq!(epoch.into_inner(), 0);
    }

    #[test]
    fn atomic_epoch_cas() {
        let atomic_epoch = AtomicEpoch::new();
        let epoch = atomic_epoch.load(Relaxed);
        let prev = atomic_epoch.compare_and_swap(Epoch::new(), epoch + 1, Relaxed);

        assert_eq!(prev, Epoch::new());
        assert_eq!(atomic_epoch.load(Relaxed), Epoch::new() + 1);
    }
}
