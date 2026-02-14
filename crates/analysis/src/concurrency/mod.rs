/// Concurrency verification module.
///
/// Provides thread interleaving enumeration, happens-before encoding,
/// and data race detection for bounded concurrency verification.
pub mod thread_encoding;

// Re-export key types for convenience
pub use thread_encoding::{Interleaving, InterleavingEvent, ThreadState};
