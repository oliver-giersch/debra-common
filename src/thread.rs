//! Concurrently accessible state of threads participating in the reclamation.

use core::fmt;
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::epoch::Epoch;

use self::State::{Active, Inactive};

const INACTIVE_BIT: usize = 0b1;

////////////////////////////////////////////////////////////////////////////////////////////////////
// ThreadState
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The concurrently accessible state of a thread, containing information about
/// the thread's current [`Epoch`] and it's [`State`].
#[derive(Debug)]
pub struct ThreadState(AtomicUsize);

impl ThreadState {
    /// Creates a new [`ThreadState`] for the current `global_epoch` and in
    /// [`Inactive`][State::Inactive] state.
    #[inline]
    pub fn new(global_epoch: Epoch) -> Self {
        Self(AtomicUsize::new(global_epoch.into_inner() | INACTIVE_BIT))
    }

    /// Returns `true` if `other` is an aliased reference to `self`.
    #[inline]
    pub fn is_same(&self, other: &Self) -> bool {
        self as *const Self == other as *const Self
    }

    /// Loads the thread's current [`Epoch`] and its ['State']
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
    pub fn load(&self, order: Ordering) -> (Epoch, State) {
        let state = self.0.load(order);
        (Epoch::with_epoch(state & !INACTIVE_BIT), State::from(state & INACTIVE_BIT == 0))
    }

    /// Stores an `epoch` and a `state` into the current thread state.
    ///
    /// `store` takes an [`Ordering`][ordering] argument, which describes the
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
    pub fn store(&self, epoch: Epoch, state: State, order: Ordering) {
        match state {
            Active => self.0.store(epoch.into_inner(), order),
            Inactive => self.0.store(epoch.into_inner() | INACTIVE_BIT, order),
        };
    }
}

impl fmt::Display for ThreadState {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (epoch, state) = self.load(Ordering::SeqCst);
        write!(f, "epoch {}, state: {}", epoch, state)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// State
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The state of a thread with regards to reading memory.
#[derive(Debug, Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum State {
    /// The thread is active, i.e. could be currently reading values from shared
    /// memory and other threads must not reclaim memory.
    Active,
    /// The thread is currently inactive, i.e. is not currently reading values
    /// from shared memory.
    Inactive,
}

impl From<bool> for State {
    #[inline]
    fn from(is_active: bool) -> Self {
        if is_active {
            Active
        } else {
            Inactive
        }
    }
}

impl fmt::Display for State {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Active => write!(f, "active"),
            Inactive => write!(f, "inactive"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering::Relaxed;

    use crate::epoch::Epoch;

    use super::{
        State::{self, Active, Inactive},
        ThreadState,
    };

    #[test]
    fn thread_state_equality() {
        let epoch = Epoch::with_epoch(128);
        let thread_state = ThreadState::new(epoch);
        let other_thread_state = ThreadState::new(epoch);

        assert!(thread_state.is_same(&thread_state));
        assert!(!thread_state.is_same(&other_thread_state));
    }

    #[test]
    fn load_thread_state() {
        let init_epoch = Epoch::with_epoch(128);
        let thread_state = ThreadState::new(init_epoch);
        let (epoch, state) = thread_state.load(Relaxed);

        assert_eq!(init_epoch, epoch);
        assert_eq!(state, Inactive);
    }

    #[test]
    fn store_thread_state() {
        let init_epoch = Epoch::with_epoch(1000);
        let thread_state = ThreadState::new(init_epoch);
        let next_epoch = init_epoch + 1;

        thread_state.store(next_epoch, Active, Relaxed);
        let (epoch, state) = thread_state.load(Relaxed);

        assert_eq!(epoch, next_epoch);
        assert_eq!(state, Active);
    }

    #[test]
    fn from_bool() {
        assert_eq!(Active, State::from(true));
        assert_eq!(Inactive, State::from(false));
    }
}
