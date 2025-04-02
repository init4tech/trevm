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
    use revm::{database::InMemoryDB, primitives::B256};
    use std::time::Duration;

    #[test]
    fn test_timeout() {
        let mut stack = InspectorSet::new();
        stack.push_back(TimeLimit::new(Duration::from_millis(15)));
        stack.push_back(SpanningInspector::at_info());
        stack.push_back(TestInspector::default());

        let mut trevm = crate::TrevmBuilder::new()
            .with_db(InMemoryDB::default())
            .with_insp(stack)
            .build_trevm()
            .unwrap()
            .fill_cfg(&NoopCfg)
            .fill_block(&NoopBlock);

        trevm.apply_eip4788(B256::repeat_byte(0xaa)).unwrap();
    }
}
