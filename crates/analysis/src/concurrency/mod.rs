pub mod channel_verification;
pub mod deadlock_detection;
pub mod happens_before;
pub mod lock_invariants;
/// Concurrency verification module.
///
/// Provides thread interleaving enumeration, happens-before encoding,
/// and data race detection for bounded concurrency verification.
pub mod thread_encoding;

// Re-export key types for convenience
pub use channel_verification::{ChannelOp, ChannelState};
pub use deadlock_detection::{DeadlockCycle, LockOrderGraph};
pub use happens_before::{EventId, MemoryAccess};
pub use lock_invariants::LockOp;
pub use thread_encoding::{Interleaving, InterleavingEvent, ThreadState};
