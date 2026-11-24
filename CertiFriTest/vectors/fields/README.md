# Reference values for the fields

A Rust program linked with Plonky3's `p3-baby-bear`, `p3-bn254` and `p3-field`
from the `plonky3/` submodule (revision `0d803737`). It prints, as Lean
definitions, the values that `CertiFriTest/P3/BabyBear.lean` and
`CertiFriTest/P3/Bn254.lean` compare the Lean fields with: sums, differences,
products, opposites, inverses and powers of fixed and pseudo-random elements,
the generators of the two-adic subgroups, and for
`BinomialExtensionField<BabyBear, 4>` the coordinates of products, inverses and
squares.

```sh
cargo run --release -- babybear
cargo run --release -- babybear-ext
cargo run --release -- bn254
```

The output is pasted into the test files; nothing reads it at build time.
