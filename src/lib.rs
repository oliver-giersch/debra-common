//! Common types and traits for implementing the DEBRA memory reclamation
//! scheme.
//!
//! # NOT INTENDED FOR GENERAL USE!
//!
//! This crate forms the common basis for both the `debra` and `debra-simple`
//! crates.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

#[cfg(not(feature = "std"))]
extern crate alloc;

pub use reclaim;

use reclaim::{LocalReclaim, Retired};

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
    type Reclaimer: LocalReclaim;

    /// Marks the associated thread as active.
    fn set_active(self);
    /// Marks the associated thread as inactive.
    fn set_inactive(self);
    /// Retires an unlinked record in the local cache.
    fn retire_record(self, record: Retired<Self::Reclaimer>);
}
