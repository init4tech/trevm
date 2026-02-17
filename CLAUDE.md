# Trevm

## Commands

- `cargo +nightly fmt` - format
- `cargo clippy --all-features --all-targets` - lint with features
- `cargo clippy --no-default-features --all-targets` - lint without
- `cargo t --all-features` - test with all features
- `cargo t --no-default-features` - test without features

Pre-commit: clippy (both feature sets) + fmt. Never use `cargo check/build`.

## Style

- Functional combinators over imperative control flow
- `let else` for early returns, avoid nesting
- No glob imports; group imports from same crate; no blank lines between imports
- Private by default, `pub(crate)` for internal, `pub` for API only; never `pub(super)`
- `thiserror` for library errors, never `anyhow` or `eyre` in library code
- `tracing` for instrumentation: instrument work items not long-lived tasks; `skip(self)` on methods
- Builders for structs with >4 fields or multiple same-type fields
- Tests: fail fast with `unwrap()`, never return `Result`; unit tests in `mod tests`
- Rustdoc on all public items with usage examples; hide scaffolding with `#`
- `// SAFETY:` comments on all unsafe blocks
- Minimize generics in user-facing API; provide concrete types where possible

## Crate Notes

- Single library crate using the **typestate pattern** to enforce correct EVM usage at compile time
- State flow: `EvmNeedsCfg` -> `EvmNeedsBlock` -> `EvmNeedsTx` -> `EvmReady` -> `EvmTransacted`
- Extensive feature flags: test with both `--all-features` and `--no-default-features`
- Key features: `call`, `concurrent-db`, `estimate_gas`, `tracing-inspectors`, `alloy-db`, `test-utils`
- Uses `#[cfg_attr(docsrs, doc(cfg(...)))]` for feature-gated documentation
