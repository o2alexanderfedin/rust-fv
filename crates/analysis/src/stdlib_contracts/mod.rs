//! Standard library contract definitions and registry.
//!
//! This module provides prebuilt formal specifications for Rust's standard
//! library types (Vec, Option, Result, HashMap, etc.) to enable verification
//! of user code that calls stdlib methods without requiring contracts on every
//! stdlib function.

pub mod hashmap;
pub mod iterator;
pub mod loader;
pub mod option;
pub mod override_check;
pub mod result;
pub mod string;
pub mod types;
pub mod vec;

pub use types::{ContractSource, StdlibContract, StdlibContractRegistry};
