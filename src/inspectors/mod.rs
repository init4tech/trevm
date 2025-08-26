mod layer;
pub use layer::Layered;

mod timeout;
pub use timeout::TimeLimit;

#[cfg(feature = "tracing-inspectors")]
mod tracing;
#[cfg(feature = "tracing-inspectors")]
pub use tracing::TracingInspectorOutput;

mod set;
pub use set::InspectorSet;

mod spanning;
pub use spanning::SpanningInspector;

mod with_output;
pub use with_output::InspectorWithOutput;

#[cfg(test)]
mod test {
    use super::*;
    use crate::{test_utils::TestInspector, NoopBlock, NoopCfg};
    use revm::{database::InMemoryDB, inspector::InspectorEvmTr, primitives::B256};
    use std::time::Duration;

    #[test]
    fn test_timeout() {
        let inspector =
            Layered::new(TimeLimit::new(Duration::from_micros(10)), SpanningInspector::at_info())
                .wrap_around(TestInspector::default());

        let mut trevm = crate::TrevmBuilder::new()
            .with_db(InMemoryDB::default())
            .with_insp(inspector)
            .build_trevm()
            .unwrap()
            .fill_cfg(&NoopCfg)
            .fill_block(&NoopBlock);

        let err = trevm.apply_eip4788(B256::repeat_byte(0xaa)).unwrap_err();
        assert!(matches!(err, revm::context::result::EVMError::Custom(_)));
        assert!(format!("{err}").contains("timeout during evm execution"));

        assert!(trevm.inner_mut_unchecked().inspector().outer().outer().has_elapsed());
    }
}
