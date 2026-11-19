# FRI test vectors from Plonky3

A Rust program that commits to matrices and opens them with Plonky3's
`TwoAdicFriPcs`, checks every proof with Plonky3's own verifier, and writes
everything a verifier needs as JSON. The JSON files next to it are its output.
The Lean tests read the JSON files; the program is needed only to regenerate
them.

Plonky3 is taken at revision `3152b14a89067c83775a8076cc262ffc48a1fd7c`, as a
git dependency in `Cargo.toml`. `Cargo.lock` pins every other crate.

## Regenerating

```
cd CertiFriTest/vectors/fri
cargo run --release
```

rewrites `small.json`, `mixed.json`, `const.json`, `wide.json` and
`primitives.json` in this directory, byte for byte. Nothing in a run is random:
matrix entries and opening points come from a seeded SplitMix64 generator in
`src/config.rs`, and with Plonky3's `parallel` features off the proof-of-work
search returns the least witness.

```
cargo run --release -- --prod <file>
```

also writes a vector of production size to `<file>` (about 1.8 MB, which is why
it is not kept here). `--out <dir>` sends the other files to another directory.

```
cargo run --release -- --bench <dir> <runs>
```

writes three vectors for timing to `<dir>` (`bench-12.json`, `bench-16.json`,
`bench-20.json`: blowup 4, 100 queries, 16 bits of grinding, first domains of
`2^12`, `2^16` and `2^20` points) and prints the mean time of Plonky3's
verifier on each over `<runs>` runs. Nothing else is written in this mode. The
Lean side is `lake exe certifri-bench <dir>/bench-16.json <runs>`, run from the
repository root.

```
cargo run --release --example find_rejection
```

recomputes the constant behind the `rejection` challenger script (see
`primitives.json` below). It takes about `2^30` BLAKE3 evaluations.

## Files

| File | Content |
| --- | --- |
| `small.json` | One batch, matrices of `2^3` and `2^2` rows (widths 2 and 3), one point each, a different point for each. `log_blowup = 1`, `log_final_poly_len = 0`, 3 queries, no grinding. 3 folding rounds. |
| `mixed.json` | Two batches. Batch 0: `2^5`, `2^3`, `2^5` rows (widths 3, 1, 2). Batch 1: `2^4`, `2^2` rows (widths 2, 4), so it is opened at shifted indices. One or two points per matrix, shared between matrices. `log_blowup = 2`, `log_final_poly_len = 1`, 5 queries, 3 bits of grinding per round, 5 before the queries. 4 folding rounds, with matrices joining after rounds 0, 1 and 2. |
| `const.json` | Matrices of one row. Batch 0: `2^3` rows (width 2) and `2^0` rows (width 1). Batch 1: `2^0` rows (width 2) alone. `log_blowup = 1`, `log_final_poly_len = 0`, 4 queries, 4 bits of grinding before the queries. Queries 0 and 2 draw the same index. |
| `wide.json` | One batch, `2^4` rows of width 130 at two points and `2^3` rows of width 5 at one. A leaf of the tall matrix is 1040 bytes and the transcript before the first challenge is 4320 bytes, so both span several 1024-byte BLAKE3 chunks. `log_blowup = 1`, `log_final_poly_len = 2`, 3 queries (two of them equal), 8 bits of grinding before the queries. |
| `primitives.json` | Known-answer values for the field, the extension, BLAKE3, the two Merkle hash functions and the challenger. |
| `prod.json` (not kept) | Two batches: `2^10` and `2^9` rows (widths 20 and 8) at two points; `2^10` and `2^8` rows (widths 12 and 6) at one. `log_blowup = 2`, `log_final_poly_len = 0`, 100 queries, 16 bits of grinding before the queries. |

The smallest matrix of `mixed.json` has `2^2` rows and not fewer: when
`log_final_poly_len > 0`, Plonky3's prover refuses a matrix whose codeword is
not taller than the final domain (`prove_fri`, `fri/src/prover.rs:91`).

## Configuration

As in `src/config.rs`:

```
Val           = Goldilocks                                 p = 2^64 - 2^32 + 1
Challenge     = BinomialExtensionField<Goldilocks, 2>      Val[X] / (X^2 - 7)
ValMmcs       = MerkleTreeMmcs<Val, u8, SerializingHasher<Blake3>,
                               CompressionFunctionFromHasher<Blake3, 2, 32>, 2, 32>
                with cap height 0: a commitment is one 32-byte root
ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>
Challenger    = SerializingChallenger64<Val, HashChallenger<u8, Blake3, 32>>
                created with an empty initial state
Pcs           = TwoAdicFriPcs<Val, Radix2Dit<Val>, ValMmcs, ChallengeMmcs>
                with max_log_arity = 1
```

## Encoding

* A field element is a JSON number holding its canonical value, `0 <= x < p`.
  Values go up to 64 bits, so a reader must not pass them through
  double-precision floats.
* An extension element is an array `[c0, c1]`, meaning `c0 + c1 X` with
  `X^2 = 7`. This is the order of Plonky3's `as_basis_coefficients_slice`.
* A digest is an array of 32 numbers, each a byte.
* Counts, indices, logarithms and bit numbers are JSON numbers.

## A vector file

```
{
  "name": string,
  "plonky3_rev": string,
  "params": {
    "log_blowup", "log_final_poly_len", "max_log_arity", "num_queries",
    "commit_proof_of_work_bits", "query_proof_of_work_bits": number
  },
  "claims": [                           one per batch, in batch order
    { "commitment": digest,
      "matrices": [                     in the order they were committed
        { "log_degree": number,         log of the row count before the blowup
          "points": [
            { "point": ext,
              "values": [ext] }         one per column
          ] } ] } ],
  "proof": {
    "commit_phase_commits": [digest],   one per folding round
    "commit_pow_witnesses": [field],    one per folding round
    "final_poly": [ext],                lowest coefficient first
    "query_pow_witness": field,
    "input_openings": [                 one per batch
      { "opened_values": [[[field]]],   [query][matrix][column]
        "opening_proof": opening_proof } ],
    "commit_phase_openings": [          one per folding round
      { "log_arity": 1,
        "sibling_values": [[ext]],      [query], one value each
        "opening_proof": opening_proof } ]
  },
  "debug": { ... }                      derived values, see below
}

opening_proof = {
  "pruned": { "sibling_hashes": [digest] },
  "paths": [[digest]]                   [query][level], leaf level first
}
```

`claims` has the shape of Plonky3's `commitments_with_opening_points`, with the
domain of a matrix replaced by the log of its size. `proof` has the shape of
`FriProof` (`fri/src/proof.rs`), with each commitment replaced by its root and
each multi-opening proof given in two forms:

* `pruned` is Plonky3's `PrunedMerklePaths`, unchanged.
* `paths` holds one full authentication path per query, such that each path
  alone verifies that query's rows. `paths[q]` has one sibling per level of the
  tree, from the leaf level up to the two children of the root. Two queries of
  the same index have the same path.

### Transcript

The challenger starts with an empty state. Both the prover and the verifier
absorb, in this order:

1. every batch commitment, in batch order (32 bytes each);
2. every opening point, in the order batch, matrix, point;
3. every claimed value, in the order batch, matrix, point, column
   (`TwoAdicFriPcs::verify`, `fri/src/two_adic_pcs.rs:684`).

Steps 1 and 2 are the caller's part and are fixed by this generator; Plonky3
starts at step 3. Then `verify_fri` (`fri/src/verifier.rs:158`):

4. sample `alpha`;
5. for each round: absorb the round's commitment, check the round's grinding
   witness with `commit_proof_of_work_bits`, sample that round's `beta`;
6. absorb the coefficients of `final_poly`, in order;
7. absorb `log_arity` of each round, each as a field element;
8. check `query_pow_witness` with `query_proof_of_work_bits`;
9. sample `num_queries` indices of `log_global_max_height` bits each, where
   `log_global_max_height = rounds + log_blowup + log_final_poly_len`. It must
   equal the largest `log_degree + log_blowup` over all matrices.

The challenger, at the level of bytes (`src/model.rs`):

* The state is two byte strings, `input` and `output`, both empty at the start.
* Absorbing bytes appends them to `input` and empties `output`. A field element
  is absorbed as its canonical value in 8 little-endian bytes, an extension
  element as `c0` then `c1`, a digest as its 32 bytes.
* A 64-bit sample takes 8 bytes off the **end** of `output`, one at a time, and
  reads them in the order taken as a little-endian integer. So it is the
  big-endian reading of the last 8 bytes of `output`. When `output` is empty it
  is first set to the BLAKE3 digest of `input`, and `input` is replaced by that
  same digest.
* A field sample is the next 64-bit sample below `p`; samples at or above `p`
  are dropped, not reduced. An extension sample is two field samples, `c0`
  first.
* A sample of `bits` bits is the low `bits` bits of one 64-bit sample, with no
  dropping.
* Checking a grinding witness with `bits = 0` does nothing and succeeds.
  Otherwise the witness is absorbed, `bits` bits are sampled, and they must be
  zero.

### Input openings

For batch `b`, matrix `m` has `log_height = log_degree + log_blowup` rows and
as many columns as there are values at its first point. Query `q` opens the
batch at `indices[q] >> (log_global_max_height - H_b)`, where `H_b` is the
largest `log_height` in the batch, and matrix `m` at that index shifted right
by `H_b - log_height`. `opened_values[q][m]` is that row.

The tree of a batch has `H_b` levels below the root. To recompute the root from
the rows of one query and its path (`root_from_path` in `src/merkle.rs`,
`verify_batch` in `merkle-tree/src/mmcs/batch.rs:156`):

* The leaf is the hash of the rows of the matrices of `log_height = H_b`,
  concatenated in batch order. The hash is BLAKE3 over the elements, each as 8
  little-endian bytes.
* At level `l`, counted from 0 at the leaves, the node is compressed with
  `path[l]`: the node on the left if bit `l` of the index is 0, on the right
  otherwise. The compression is BLAKE3 over the 64 bytes `left ++ right`.
* If some matrices have `log_height = H_b - l - 1`, the result is compressed
  once more: itself on the left, the hash of the concatenated rows of those
  matrices on the right.

### Reduced openings

For query `q` and each `log_height` that occurs, in increasing order of batch,
matrix, point and column, with one running power of `alpha` per height that
starts at 1:

```
x       = 7 * g^bitrev(index, log_height)     g = two_adic_generator(log_height)
          index = indices[q] >> (log_global_max_height - log_height)
          bitrev reverses the low log_height bits
sum    += alpha_pow * (value_at_point - opened_value) / (point - x)
alpha_pow *= alpha
```

A sum at `log_height = log_blowup` exists only for matrices of one row, and
must be zero.

### Folding

Query `q` starts from the sum at `log_global_max_height` with
`index = indices[q]`. Round `r` commits to one matrix of two extension columns
and `2^(log_global_max_height - r - 1)` rows. The proof does not carry the
opened row, only the value the verifier does not already hold:

```
row     = [folded, sibling]  if index is even,  [sibling, folded]  otherwise
          sibling = sibling_values[q][0]
index   = index >> 1                           the row that is opened
x       = g^bitrev(index, h)                   h = log of the row count,
                                               g = two_adic_generator(h + 1)
folded  = (row[0] + row[1]) / 2 + beta * (row[0] - row[1]) / (2 x)
folded += beta^2 * sum                         if there is a sum at log_height h
```

After the last round, `final_poly` evaluated at
`two_adic_generator(H)^bitrev(index, H)`, with
`H = log_blowup + log_final_poly_len`, must equal `folded`.

The opened row of round `r` is checked against `commit_phase_commits[r]` as a
tree with a single matrix of four field columns: the row is hashed as
`row[0].c0, row[0].c1, row[1].c0, row[1].c1`.

### The pruned form

`sibling_hashes` is one flat list for all queries. It carries no index and no
length. Read it as follows (`walk_frontier`, `merkle-tree/src/pruning.rs:130`):

* The frontier of level 0 is the set of distinct opened indices.
* At each level, take the parents of the frontier nodes in increasing order.
  For each, look at its left child, then its right child. A child that is not
  in the frontier takes the next digest of the list. A child that is in the
  frontier takes nothing: the verifier has computed it.
* The parents are the frontier of the next level.

A level where both children of every parent are opened contributes nothing, so
the list can be empty (`const.json`, batch 1). `paths` is this list unpacked,
with the computed siblings filled in (`restore_paths` in `src/merkle.rs`).

### `debug`

Values the verifier derives, for locating a mismatch. None of them is an input.

```
"debug": {
  "log_global_max_height": number,
  "alpha": ext,
  "betas": [ext],                       one per round
  "indices": [number],                  one per query
  "input_batches": [                    one per batch
    { "dimensions": [ { "width": number, "log_height": number } ],
      "indices": [number] } ],          the index each query opens the batch at
  "reduced_openings": [                 [query], by decreasing log_height
    [ { "log_height": number, "value": ext } ] ],
  "rounds": [                           one per round
    { "log_height": number,             log of the row count of the round's matrix
      "indices": [number],              the row each query opens
      "rows": [[ext, ext]],             that row
      "folded": [ext] } ],              the value each query carries out of the round
  "final_points": [field],              [query], where final_poly is evaluated
  "final_evals": [ext]                  [query], its value there
}
```

## `primitives.json`

```
{
  "plonky3_rev": string,
  "goldilocks": {
    "modulus", "generator", "two_adicity": number,
    "two_adic_generators": [field],     index k: two_adic_generator(k), k = 0..32
    "add": [ { "a", "b", "sum" } ],
    "sub": [ { "a", "b", "difference" } ],
    "mul": [ { "a", "b", "product" } ],
    "inv": [ { "a", "inverse" } ],
    "exp": [ { "base", "exponent", "power" } ]      exponent is a plain integer
  },
  "extension": {
    "non_residue": 7,
    "add", "sub", "mul": as above, over ext
    "inv": [ { "a", "inverse" } ]
  },
  "blake3": [ { "len": number, "digest": digest } ],
  "leaf_hash": [ { "values": [field], "digest": digest } ],
  "compress": [ { "left": digest, "right": digest, "digest": digest } ],
  "challenger": [ { "name": string, "steps": [step] } ]
}
```

* `blake3`: the input of length `len` has byte `i` equal to `i mod 251`, as in
  the official BLAKE3 test vectors.
* `leaf_hash`: `SerializingHasher<Blake3>` on a slice of field elements. All
  inputs but the last are `values[i] = (i + 1) * 0x0123456789ABCDEF mod p`.
* `compress`: `CompressionFunctionFromHasher<Blake3, 2, 32>` on two digests.
* `challenger`: each script starts from the empty state. A step is one of

  ```
  { "op": "observe_base",   "value": field }
  { "op": "observe_ext",    "value": ext }
  { "op": "observe_digest", "value": digest }
  { "op": "sample_ext",     "result": ext }
  { "op": "sample_bits",    "bits": number, "result": number }
  { "op": "check_witness",  "bits": number, "witness": field, "result": bool }
  ```

  and also carries `"input_buffer"` and `"output_buffer"`, the two byte strings
  of the state after the step.

  * `main` covers every operation, a witness check at zero bits, a witness that
    passes and one that fails, and runs of samples that pass the end of one
    digest.
  * `empty` samples before anything is absorbed.
  * `rejection` absorbs the least field element after which one of the first
    four 64-bit samples is at or above `p` (it is the fourth). The second
    extension sample therefore takes its `c1` from the next digest.
  * `bits_keep_large_samples` absorbs the same element and samples bits: the
    fourth sample, of 63 bits, is cut from that same out-of-range value.

## What the generator checks

Every run asserts, for each vector:

* Plonky3's `pcs.verify` accepts the proof, and rejects it when one claimed
  value is changed.
* A second verifier (`src/reference.rs`), written against nothing but the
  content of the file and the byte-level definitions above, accepts it with the
  paths, and rejects a changed claimed value and a changed path.
* The challenges of that verifier equal those obtained by replaying the steps
  of `verify_fri` on Plonky3's own challenger, and its folded values equal
  those of Plonky3's `fold_row`.
* Plonky3's `verify_multi_batch` accepts every pruned proof at the replayed
  indices.
* Plonky3's one-index `verify_batch` accepts every restored path, and for input
  batches the restored path equals the one `open_batch` returns.

and, for the primitives, that the byte-level leaf hash, compression and
challenger agree with the Plonky3 types on every value written.
