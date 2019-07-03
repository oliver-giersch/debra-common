//! Common types, traits and base functionality for the DEBRA reclamation
//! scheme.
//!
//! This crate forms the common basis for both the `debra` and `debra-simple`
//! crates.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(test)]
extern crate std;

pub use arrayvec;
pub use reclaim;

use reclaim::{Reclaim, Retired};

pub mod bag;
pub mod epoch;
pub mod thread;

/// A trait for abstracting over different ways for accessing thread local
/// state.
pub trait LocalAccess
where
    Self: Clone + Copy + Sized,
{
    /// The concrete reclamation scheme type.
    type Reclaimer: Reclaim;

    /// Returns `true` if the current thread is already active.
    fn is_active(self) -> bool;
    /// Marks the associated thread as active.
    fn set_active(self);
    /// Marks the associated thread as inactive.
    fn set_inactive(self);
    /// Retires an unlinked record in the local cache.
    fn retire_record(self, record: Retired<Self::Reclaimer>);
}

include!(concat!(env!("OUT_DIR"), "/build_constants.rs"));

/// The value of the configurable per-thread size for individual bags storing
/// cached retired records.
pub const EPOCH_CACHE_SIZE: usize = DEBRA_EPOCH_CACHE_SIZE;
