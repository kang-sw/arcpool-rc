pub mod api;
pub mod unsafe_ref_cell;

mod detail;

pub use api::*;

// TODO: ArcSwap RefCnt adapter

#[cold]
fn cold_path() {}
