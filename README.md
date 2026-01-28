# verified-graphs

This crate contains code for graphs (undirected and directied) verified from
first principles using [Verus](https://github.com/verus-lang/verus). The graph
specifications and proofs strictly follow those found in the [classic text on graph theory](https://www.cambridge.org/us/universitypress/subjects/mathematics/discrete-mathematics-information-theory-and-coding/graph-theory?format=PB&isbn=9780521794893)
by W. T. Tutte. The code only covers finite graphs for the time being.

The goal of the crate is to provide abstract graph types that other
crates can refine their data structures to and accompanying proofs to
help verify the correctness of operations on the data structures (e.g.,
insertion into a binary tree maintains the invariant of it being an
[arborescence](https://en.wikipedia.org/wiki/Arborescence_(graph_theory))).

## Development

This crate provides a
[devcontainer](https://code.visualstudio.com/docs/devcontainers/containers)
installed with [Rust](https://www.rust-lang.org/tools/install) and
[Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md).

To verify the crate:
```bash
cargo verus verify -- --expand-errors
```

## Contributing

This crate is still in the early stages of development, and we welcome
suggestions and contributions from the community. If you are interested in
contributing, please feel free to open and issue or a pull request.
