# trevm

## Commands

- `cargo +nightly fmt` - format
- `cargo clippy -p trevm --all-features --all-targets` - lint with features
- `cargo clippy -p trevm --no-default-features --all-targets` - lint without
- `cargo t -p trevm` - test

Pre-push: clippy (both feature sets) + fmt. Never use `cargo check/build`.

### Pre-push Checks (enforced by Claude hook)

A Claude hook in `.claude/settings.json` runs `.claude/hooks/pre-push.sh`
before every `git push`. The push is blocked if any check fails. The checks:

- `cargo +nightly fmt -- --check`
- `cargo clippy -p trevm --all-targets --all-features -- -D warnings`
- `cargo clippy -p trevm --all-targets --no-default-features -- -D warnings`
- `RUSTDOCFLAGS="-D warnings" cargo doc -p trevm --no-deps`

Clippy and doc warnings are hard failures.

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

## Versioning

Trevm uses semver. While pre-1.0, the MINOR version tracks revm's MAJOR
version (e.g. trevm `0.34.x` targets revm `34.x.x`). Breaking changes go
in PATCH versions to preserve this relationship, documented in GitHub
release notes. Always bump the patch version for breaking changes.
