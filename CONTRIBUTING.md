# Contributing to Trevm

:balloon: Thanks for your help improving the project! We are so happy to have
you!

## Conduct

This repo adheres to the [Rust Code of Conduct][coc]. This describes
the _minimum_ behavior expected from all contributors. Failure to maintain civil
behavior will result in a ban.

[coc]: https://www.rust-lang.org/policies/code-of-conduct

## Pull Requests

Before making a large change, it is usually a good idea to first open an issue
describing the change to solicit feedback and guidance. This will increase the
likelihood of the PR getting merged.

When opening a PR **please select the "Allow Edits From Maintainers" option**.
We maintain code quality and style standards, and require commit signing. This
option allows us to make small changes to your PR to bring it in line with
these standards. It helps us get your PR in faster, and with less work from you.

## Development Basics

Before submitting a PR we recommend you run the following commands to ensure
your code is properly formatted and passes all tests:

```sh
cargo +nightly fmt --all
cargo clippy --all-features
cargo test --all-features
cargo test --no-default-features
```

### Contributions Related to Spelling, Grammar, and other trivial changes

At this time, we will not be accepting contributions that only fix spelling or
grammatical errors in documentation, code or
elsewhere.
