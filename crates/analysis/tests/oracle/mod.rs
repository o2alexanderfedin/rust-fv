//! Property-based oracle tests for stdlib contract soundness.
//!
//! These tests validate that all stdlib contract postconditions hold for real
//! stdlib operations. Each oracle test:
//! 1. Generates random inputs via proptest
//! 2. Executes the real stdlib operation
//! 3. Asserts the postcondition from the stdlib contract holds
//!
//! If any postcondition fails, the corresponding contract is UNSOUND.

mod hashmap_oracle;
mod iterator_oracle;
mod option_result_oracle;
mod vec_oracle;
