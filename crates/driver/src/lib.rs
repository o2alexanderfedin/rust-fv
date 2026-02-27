//! rust-fv-driver library exports for testing.
//!
//! Exposes cache, invalidation, parallel, json_output, cex_render, and types modules
//! for integration tests. The callbacks module is NOT exported here because it depends
//! on rustc internals (rustc_driver, rustc_middle) which are only available when
//! building as a rustc driver plugin.

pub mod cache;
pub mod cex_render;
pub mod invalidation;
pub mod json_output;
pub mod parallel;
pub mod types;
