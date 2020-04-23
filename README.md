# accumulator

Modified version of [accumulator](https://github.com/cambrian/accumulator) that allows accumulating without hash-to-prime and exposes additional info needed for the protocols in [CPSNARKs-Set](https://github.com/kobigurk/cpsnarks-set).

Cryptographic accumulators in Rust, implemented over a generic group interface. Batteries (RSA and
class group implementations) included!

## Installation
```toml
# Cargo.toml
[dependencies]
accumulator = { git = "https://github.com/cambrian/accumulator.git", tag = "v0.2.1" }
```

## Docs
Available [here](https://cambrian.dev/accumulator/docs), and feel free to reach out with any
questions.

## Demo
We have a [proof-of-concept](https://github.com/cambrian/accumulator-demo) for stateless Bitcoin
nodes.

## Contributing
Please see our
[contribution guide](https://github.com/cambrian/accumulator/blob/master/CONTRIBUTING.md). We are
looking for long-term maintainers!
