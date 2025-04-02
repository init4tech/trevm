mod timeout;
pub use timeout::TimeLimit;

mod set;
pub use set::InspectorSet;

mod spanning;
pub use spanning::SpanningInspector;

mod layer;
pub use layer::Layered;

#[cfg(test)]
mod test {
    use super::*;
    use crate::{test_utils::TestInspector, NoopBlock, NoopCfg};
    use revm::{database::InMemoryDB, inspector::InspectorEvmTr, primitives::B256};
    use std::time::Duration;

    #[test]
    fn test() {
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

        trevm.apply_eip4788(B256::repeat_byte(0xaa)).unwrap();

        dbg!(trevm.inner_mut_unchecked().ctx_inspector().1);
    }
}
