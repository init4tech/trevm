use crate::{helpers::Ctx, inspectors::InspectorWithOutput};
use alloy::rpc::types::trace::geth::FourByteFrame;
use revm::Database;
use revm_inspectors::tracing::{
    CallTraceArena, FourByteInspector, GethTraceBuilder, ParityTraceBuilder, TracingInspector,
};

/// Output produced by the [`TracingInspector`].
#[derive(Clone, Debug)]
pub struct TracingInspectorOutput {
    traces: CallTraceArena,
}

impl TracingInspectorOutput {
    /// Creates a new output instance.
    pub fn new(traces: CallTraceArena) -> Self {
        Self { traces }
    }

    /// Returns a reference to the traces produced by the inspector.
    pub fn traces(&self) -> &CallTraceArena {
        &self.traces
    }

    /// Consumes the output and produces a Parity trace builder.
    pub fn into_parity_builder(self) -> ParityTraceBuilder {
        // NB: the second arguments are actually currently unused. This is
        // weird.
        ParityTraceBuilder::new(self.traces.into_nodes(), None, Default::default())
    }

    /// Consumes the output and produces a Geth trace builder.
    pub fn into_geth_builder(self) -> GethTraceBuilder<'static> {
        GethTraceBuilder::new(self.traces.into_nodes())
    }
}

impl<Db: Database> InspectorWithOutput<Ctx<Db>> for TracingInspector {
    type Output = TracingInspectorOutput;

    fn has_output(&self) -> bool {
        self.traces().nodes().len() > 0
    }

    fn reset_output(&mut self) {
        self.fuse();
    }

    fn take_output(&mut self) -> Self::Output {
        let this = self.clone();
        self.fuse();
        TracingInspectorOutput::new(this.into_traces())
    }
}

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
