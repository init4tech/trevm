use crate::{helpers::Ctx, Trevm};
use revm::{inspector::CountInspector, Database};

/// An inspector that can produce an output value after EVM execution.
pub trait InspectorWithOutput<CTX>: revm::inspector::Inspector<CTX> {
    /// The type of output produced by the inspector.
    type Output;

    /// Returns `true` if the inspector has a valid output value.
    fn has_output(&self) -> bool;

    /// Reset the output value to the default state, discarding any current
    /// value.
    fn reset_output(&mut self) {
        self.take_output();
    }

    /// Take the output value from the inspector, resetting it to the default
    /// state.
    fn take_output(&mut self) -> Self::Output;
}

impl<Db: Database, Insp> Trevm<Db, Insp>
where
    Insp: InspectorWithOutput<Ctx<Db>>,
{
    /// Take the output value from the inspector.
    ///
    /// This will also reset the output value in the inspector.
    pub fn take_output(&mut self) -> Insp::Output {
        self.inspector_mut().take_output()
    }
}

impl<Ctx> InspectorWithOutput<Ctx> for CountInspector {
    type Output = Self;

    fn has_output(&self) -> bool {
        self.total_opcodes() > 0
    }

    fn reset_output(&mut self) {
        self.clear();
    }

    fn take_output(&mut self) -> Self::Output {
        std::mem::take(self)
    }
}
