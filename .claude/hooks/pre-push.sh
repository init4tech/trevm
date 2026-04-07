#!/usr/bin/env bash
set -euo pipefail

# Consume stdin (hook protocol)
cat > /dev/null

cd "$(dirname "$0")/../.."

echo "Running pre-push checks..." >&2

if ! cargo +nightly fmt -- --check 2>&1; then
    echo "Format check failed. Run 'cargo +nightly fmt' to fix." >&2
    exit 2
fi

if ! cargo clippy -p trevm --all-targets --all-features -- -D warnings 2>&1; then
    echo "Clippy (--all-features) failed." >&2
    exit 2
fi

if ! cargo clippy -p trevm --all-targets --no-default-features -- -D warnings 2>&1; then
    echo "Clippy (--no-default-features) failed." >&2
    exit 2
fi

if ! RUSTDOCFLAGS="-D warnings" cargo doc -p trevm --no-deps 2>&1; then
    echo "Doc check failed." >&2
    exit 2
fi

echo "All pre-push checks passed." >&2
exit 0
