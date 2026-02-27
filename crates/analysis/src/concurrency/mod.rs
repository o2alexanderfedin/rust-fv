pub mod channel_verification;
pub mod deadlock_detection;
pub mod happens_before;
pub mod lock_invariants;
pub mod rc11;
/// Concurrency verification module.
///
/// Provides thread interleaving enumeration, happens-before encoding,
/// and data race detection for bounded concurrency verification.
/// Also provides RC11 weak memory model SMT encoding primitives.
pub mod thread_encoding;

// Re-export key types for convenience
pub use channel_verification::{ChannelOp, ChannelState};
pub use deadlock_detection::{DeadlockCycle, LockOrderGraph};
pub use happens_before::{EventId, MemoryAccess};
pub use lock_invariants::LockOp;
pub use rc11::{has_non_seqcst_atomics, weak_memory_smt_logic};
pub use thread_encoding::{Interleaving, InterleavingEvent, ThreadState};
