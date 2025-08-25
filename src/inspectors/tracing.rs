use crate::{helpers::Ctx, inspectors::InspectorWithOutput};
use alloy::rpc::types::trace::geth::FourByteFrame;
use revm::Database;
use revm_inspectors::tracing::FourByteInspector;

impl<Db: Database> InspectorWithOutput<Ctx<Db>> for FourByteInspector {
    type Output = FourByteFrame;

    fn has_output(&self) -> bool {
        !self.inner().is_empty()
    }

    fn reset_output(&mut self) {
        *self = Self::default();
    }

    fn take_output(&mut self) -> Self::Output {
        std::mem::take(self).into()
    }
}
