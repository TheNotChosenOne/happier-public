# happier

[![CI](https://github.com/TheNotChosenOne/happier/actions/workflows/ci.yml/badge.svg)](https://github.com/TheNotChosenOne/happier/actions/workflows/ci.yml)

A SAT solver designed to be zero dependency, zero unsafe, no_std, and wasm compatible.
Note that no_std and zero unsafe require disabling default features.
Definitely not state of the art, but has some efficiencies like clause learning.

Supports the unique-ish operation of "which of these variables can be positive"
for my own purposes.

## Testing

Integration tests, four `cargo-fuzz` targets, differential checking against
minisat via `rustsat`, runtime invariants under the `contracts` feature, and a
`cargo-mutants` configuration.

## Benchmarks

See [`benches/README.md`](benches/README.md)
