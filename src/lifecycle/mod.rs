mod cycles;
pub use cycles::{CancunLifecycle, PragueLifecycle, ShanghaiLifecycle};

mod output;
pub use output::BlockOutput;

mod r#trait;
pub use r#trait::Lifecycle;
