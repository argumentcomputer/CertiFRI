# STARK test vectors from multi-stark

A Rust program that proves small statements with the `multi-stark` prover,
checks every proof with multi-stark's own verifier, and writes everything that
verifier reads as JSON. The JSON files next to it are its output. The Lean
tests read the JSON files; the program is needed only to regenerate them.

multi-stark is the crate `multi-stark/` of this repository, a path dependency
in `Cargo.toml`, with its `parallel` and `cuda` features off. It is revision
`3515632f1dc1a5764b60fc0146ea2226bb6fc32d` of
`https://github.com/argumentcomputer/multi-stark.git`. It builds on Plonky3
at revision `3152b14a89067c83775a8076cc262ffc48a1fd7c`. `Cargo.lock` pins every
other crate. multi-stark requires Rust 1.98; `rust-toolchain.toml` selects
1.98.1, the toolchain multi-stark pins for itself.

## Regenerating

```
cd CertiFriTest/vectors/stark
cargo run --release
```

rewrites `lookup.json`, `fixed.json`, `batch.json` and `sparse.json` in this
directory, byte for byte. Nothing in a run is random: the circuits and their
traces are fixed in `src/circuits.rs` and `src/main.rs`, and multi-stark's
challenger returns the least grinding witness. `--out <dir>` sends the files
to another directory.

## Files

| File | Protocol | Content |
| --- | --- | --- |
| `lookup.json` | single proof | The Fibonacci system. `sequence` has `2^3` rows and pushes three of them; `reader` has `2^2` rows, pulls those three, and pulls two claims, `[5, 5]` and `[7, 13]`. No fixed columns. Quotient degree 1 for both circuits. `log_blowup = 1`, `log_final_poly_len = 0`, 3 queries, no grinding. 3 folding rounds. |
| `fixed.json` | single proof | The cubes system. `sums` (`2^2` rows, three lookups grouped by two, two extension constraints), `table` (`2^3` rows, two fixed columns), `rounds` (`2^2` rows, one fixed column, no lookups, two extension constraints) are active; `spare`, which has no fixed columns, is inactive. Three claims. Quotient degrees 2, 1 and 4. `log_blowup = 2`, `log_final_poly_len = 0`, 4 queries, 2 bits of grinding per round, 4 before the queries. 3 folding rounds. Queries 0 and 3 draw the same index. |
| `batch.json` | batch | The Fibonacci system in two shards. Shard 0: `sequence` (`2^3` rows, pushing rows 2, 4, 5, 7) and `reader` (`2^1` rows, pulling row 2 and the claim `[2, 1]` of its header); 3 folding rounds. Shard 1: `reader` alone (`2^1` rows, pulling rows 5 and 7 and the message `[5, 5]`), `sequence` inactive, no claim; 1 folding round. The preamble has two messages: `[5, 5]` with multiplicity 1 and `[4, 3, 5]` with multiplicity -1. `log_blowup = 1`, `log_final_poly_len = 0`, 3 queries, 1 bit of grinding per round. |
| `sparse.json` | single proof | The cubes system with `sums` (`2^2` rows) and `table` (`2^3` rows) active, `spare` and `rounds` inactive. The fixed trace of `rounds` is still committed, and is opened at one point. Three claims. `log_blowup = 2`, `log_final_poly_len = 1`, 3 queries, 3 bits of grinding before the queries. 2 folding rounds, a final polynomial of two coefficients. |

In shard 1 of `batch.json` the tallest trace has two rows. Every committed
polynomial then has degree at most one, the function FRI folds in its only
round is constant, and the value of that round's challenge has no effect on
the verifier's result.

## The systems

Both are defined in `src/circuits.rs` as `CircuitInputs`. No lookup expression
uses a row selector: multi-stark evaluates a selector as 0 or 1 when it builds
the lookup witness and as Plonky3's unnormalized selector polynomial in the
constraints, and its verifier rejects the resulting proof.

**Fibonacci** (`lookup.json`, `batch.json`), constraint degree 2 throughout:

* Circuit 0, `sequence`, main columns `i, a, b, s`. Row `i` holds `a = F_i` and
  `b = F_(i+1)`. Constraints: on the first row `i = 0`, `a = 0`, `b = 1`; on
  transitions `i' = i + 1`, `a' = b`, `b' = a + b`; `s` is boolean; on the last
  row `s = 1`. One lookup: push `[i, a, b]` with multiplicity `s`.
* Circuit 1, `reader`, main columns `n, f, g, m, c`. Constraints: `m` and `c`
  are boolean, `c (m - 1) = 0`. Two lookups: pull `[n, f, g]` with multiplicity
  `m`, pull `[n, f]` with multiplicity `c`. A claim is `[n, F_n]`.

**Cubes** (`fixed.json`, `sparse.json`):

* Circuit 0, `sums`, main columns `a, b, a3, b3, s`. Constraint: `s` is
  boolean. Three lookups with `lookup_group_size = 2`: push `[a, a3]`, push
  `[b, b3]`, pull `[100, a3 + b3]`, all with multiplicity `s`. Stage 2 has two
  accumulator slots; slot 0 enters the group of the first two lookups and slot
  1 the group of the third. Two extension constraints, with `S0`, `S1` the
  extension values of the two slots: `is_first_row * S0 = 0` and
  `is_first_row * S0 * S1 = 0`. The second multiplies two values that are not
  embedded base values, so its expansion is the three-multiplication form.
  Constraint degree 3.
* Circuit 1, `table`, fixed columns `x, x^3` for `x = 0..8`, main column `m`.
  Constraint: on transitions `x' = x + 1`, read from the next fixed row. One
  lookup: pull `[x, x^3]` with multiplicity `m`. Constraint degree 2.
* Circuit 2, `spare`, main columns `u, v`. Constraint: `u` is boolean. One
  lookup: pull `[200, v]` with multiplicity `u`. It never has a trace.
* Circuit 3, `rounds`, fixed column `k = 3, 5, 7, 11`, main columns `x, y`.
  Constraints: on the first row `x = 2` and `y = k`; on transitions
  `x' = x^5 + k` and `y' = y + k'`; on the last row `y = 26`. No lookups. Two
  extension constraints, on the public values and the stage-2 column:
  `acc_out - acc_in = 0` and `(S0' - S0) * gamma = 0`. Constraint degree 5.

A claim of the cubes system is `[100, a^3 + b^3]`.

## Configuration

`multi_stark::types::GoldilocksBlake3Config`. Field, extension, hashes, Merkle
trees and `TwoAdicFriPcs` are those of the FRI vectors (`../fri/README.md`,
"Configuration"), with `cap_height = 0` and `max_log_arity = 1`. The challenger
is the same `SerializingChallenger64` over BLAKE3, but its initial state is not
empty: its input buffer starts as the bytes of `seed`.

## Encoding

As in `../fri/README.md`:

* A field element is a JSON number holding its canonical value, `0 <= x < p`.
  Values go up to 64 bits.
* An extension element is an array `[c0, c1]`, meaning `c0 + c1 X` with
  `X^2 = 7`.
* A digest is an array of 32 numbers, each a byte. A commitment is a Merkle cap
  of height 0 and is written as its one digest.
* Counts, indices, logarithms and bit numbers are JSON numbers. A boolean is a
  JSON boolean.

## A vector file

```
{
  "name": string,
  "multi_stark_rev": string, "plonky3_rev": string,
  "seed": [number],                 bytes of the challenger's initial state
  "params": { "log_blowup", "cap_height", "log_final_poly_len", "max_log_arity", "num_queries",
              "commit_proof_of_work_bits", "query_proof_of_work_bits": number },
  "max_log_degree": number,         config.max_log_degree(), that is 32 - log_blowup
  "extension_degree": 2,
  "system": {
    "preprocessed_commit": digest | null,
    "preprocessed_indices": [number | null],      one per circuit
    "circuits": [ {
        "main_width", "preprocessed_width", "preprocessed_height", "num_lookups",
        "stage_2_width", "num_publics", "lookup_group_size", "constraint_count",
        "max_constraint_degree", "quotient_degree": number,
        "graph": {
          "nodes": [node],
          "zeros": [number],                          node ids
          "lookups": [ { "multiplicity": number, "args": [number] } ]   node ids
        } } ] },
  "single": { "claims": [[field]], "proof": stark_proof, "debug": debug },
  "batch": {
    "preamble": {
      "headers": [ { "active": [bool], "stage_1_trace": digest, "log_degrees": [number],
                     "claims": [[field]] } ],
      "messages": [ { "args": [field], "multiplicity": field } ] },
    "proofs": [stark_proof],
    "debug": { "lookup_challenge": ext, "fingerprint_challenge": ext, "shards": [debug] }
  }
}

node =  { "op": "const", "value": field }
      | { "op": "var", "source": "preprocessed" | "main" | "stage2", "next": bool, "index": number }
      | { "op": "public", "index": number }
      | { "op": "is_first_row" } | { "op": "is_last_row" } | { "op": "is_transition" }
      | { "op": "add" | "sub" | "mul", "a": number, "b": number }
      | { "op": "neg", "a": number }

stark_proof = {
  "active": [bool],
  "commitments": { "stage_1_trace": digest, "stage_2_trace": digest, "quotient_chunks": digest },
  "intermediate_accumulators": [ext],
  "log_degrees": [number],
  "quotient_opened_values": [[[ext]]],             [matrix][point][column]
  "preprocessed_opened_values": [[[ext]]] | null,
  "stage_1_opened_values": [[[ext]]],
  "stage_2_opened_values": [[[ext]]],
  "opening_proof": fri_proof
}

fri_proof = {
  "commit_phase_commits": [digest],   one per folding round
  "commit_pow_witnesses": [field],    one per folding round
  "final_poly": [ext],                lowest coefficient first
  "query_pow_witness": field,
  "input_openings": [                 one per commitment
    { "opened_values": [[[field]]],   [query][matrix][column]
      "opening_proof": opening_proof } ],
  "commit_phase_openings": [          one per folding round
    { "log_arity": 1,
      "sibling_values": [[ext]],      [query], one value each
      "opening_proof": opening_proof } ]
}

opening_proof = { "pruned": { "sibling_hashes": [digest] } }

debug = {
  "lookup_challenge": ext,            beta
  "fingerprint_challenge": ext,       gamma
  "constraint_challenge": ext,        alpha of the constraint folding
  "zeta": ext,
  "fri_alpha": ext,                   the first challenge sampled inside pcs.verify
  "fri_betas": [ext],                 one per folding round
  "fri_indices": [number]             one per query
}
```

Exactly one of `single` and `batch` is present; the other key is absent.
`fri_proof` is the `proof` object of `../fri/README.md` without the `paths`
form of the opening proofs. Every `debug` object has all seven fields: in a
batch the two lookup challenges of each shard repeat those of `batch.debug`.

### `system`

`system` is the verifier's view of `System`: the fields of each `Circuit` that
the verifier reads, and `Circuit::quotient_degree()`.

* `preprocessed_indices[i]` is the position of circuit `i`'s fixed trace among
  the matrices of `preprocessed_commit`, or `null` if it has none.
  `preprocessed_commit` is `null` when no circuit has one.
* `graph.nodes` is in topological order: the operands `a`, `b` of a node are
  ids of earlier nodes. `index` of a `var` node is a column of the named
  matrix; for `stage2` it is a base column, the accumulator slot `s` being the
  columns `2s` and `2s + 1`.
* `index` of a `public` node selects one of eight values: the coordinates
  `c0, c1` of beta (0, 1), of gamma (2, 3), of the accumulator entering the
  circuit (4, 5) and of the accumulator leaving it (6, 7).
* The selector nodes are Plonky3's `selectors_at_point`, which are not
  normalized. With `n = 2^log_degree`, `g` the generator of the trace domain
  and `Z = zeta^n - 1`: `is_first_row = Z / (zeta - 1)`,
  `is_last_row = Z / (zeta - 1/g)`, `is_transition = zeta - 1/g`.
* `zeros` are the roots of the circuit's own constraints, in the order they
  are folded. An extension constraint contributes its two coordinates. The
  lookup constraints are not in the graph: the verifier computes their
  `stage_2_width` values from `lookups` and `lookup_group_size`
  (`logup_constraint_values`), and folds them after `zeros`.
  `constraint_count = len(zeros) + stage_2_width`. The values `v_0, v_1, ...`
  are folded as `(v_0 alpha + v_1) alpha + ...`, and the result divided by `Z`
  equals the quotient at `zeta`.
* `lookups[j].multiplicity` and `lookups[j].args` are node ids. A pull has the
  negated multiplicity as its node.

### `stark_proof`

`active[i]` says whether circuit `i` is covered. Let the active circuits be
numbered in increasing order of `i`; that number is a circuit's active
position. `intermediate_accumulators`, `log_degrees`, `stage_1_opened_values`,
`stage_2_opened_values` and `quotient_opened_values` have one entry per active
circuit, at its active position.

With `g` the generator of the trace domain of an active circuit,
`two_adic_generator(log_degree)`:

* `stage_1_opened_values[pos]` has two points, `zeta` and `zeta * g`, of
  `main_width` values each.
* `stage_2_opened_values[pos]` has the same two points, of `stage_2_width`
  values each.
* `quotient_opened_values[pos]` has one point, `zeta`, of
  `2 * quotient_degree` values. Chunk `i` of the quotient is
  `row[2i] + X * row[2i + 1]`, and the quotient at `zeta` is the sum of
  `zeta^(i * 2^log_degree) * chunk_i`.
* `preprocessed_opened_values` is `null` when `preprocessed_commit` is. It has
  one entry per fixed trace, at the position `preprocessed_indices` gives,
  whether its circuit is active or not. An active circuit's entry has the two
  points `zeta` and `zeta * g`, of `preprocessed_width` values each. An
  inactive circuit's entry has the one point `zeta`; its matrix has
  `preprocessed_height` rows, and its values enter no constraint.

This configuration opens the next row of every main and fixed matrix of an
active circuit, whether or not a constraint reads it.

`opening_proof.input_openings` has one entry per commitment, in the order
`pcs.verify` is given them: stage 1, stage 2, quotient, then the fixed traces
if `preprocessed_commit` is not `null`. In the terms of `../fri/README.md`,
these are the batches of `claims`; the matrices of each are the entries of the
matching `*_opened_values`, in order, with `log_degree` the circuit's (for an
inactive fixed trace, the log of `preprocessed_height`), and the points as
above.

The accumulator starts as the sum of `1 / (beta + sum_i claim[i] gamma^i)` over
the claims. The circuit at active position `pos` takes it to
`intermediate_accumulators[pos]`. In a single proof the last one is zero.

### `batch`

`headers[k]` describes `proofs[k]`: `active`, `stage_1_trace` and
`log_degrees` equal the proof's `active`, `commitments.stage_1_trace` and
`log_degrees`. The accumulator of shard `k` starts from the claims of
`headers[k]`. The last intermediate accumulators of the shards and the sum of
`multiplicity / (beta + sum_i args[i] gamma^i)` over `messages` add up to zero.

### Transcript

The challenger is the one of `../fri/README.md` ("Transcript"), started with
`input = seed`. `seed` is the 14 bytes of `multi-stark/v0` followed by the
seven values of `params`, in the order written, each as 8 little-endian bytes.
A count, a length, a flag, a logarithm or an index is absorbed as one field
element.

A single proof (`System::verify_multiple_claims`,
`System::verify_after_challenges`):

1. the shape of the system (`System::observe_shape`): the number of circuits,
   then for each circuit `constraint_count`, `max_constraint_degree`,
   `preprocessed_height`, `preprocessed_width`, `main_width`, `stage_2_width`,
   `lookup_group_size`;
2. each entry of `active`, as 0 or 1;
3. `preprocessed_commit`, if not `null`;
4. `commitments.stage_1_trace`;
5. each entry of `log_degrees`;
6. the number of claims, then for each claim its length and its elements;
7. sample beta, absorb beta, sample gamma, absorb gamma;
8. `commitments.stage_2_trace`;
9. each entry of `intermediate_accumulators`;
10. sample alpha (`constraint_challenge`);
11. `commitments.quotient_chunks`;
12. sample `zeta`;
13. every opened value, in the order stage 1, stage 2, quotient, fixed, and
    within each `[matrix][point][column]`;
14. sample `fri_alpha`, and continue as steps 5 to 9 of the transcript of
    `../fri/README.md`, which give `fri_betas` and `fri_indices`.

A batch (`System::batch_challenger`, `verify_batch_shard_from`) replaces steps
1 to 7 by:

1. the shape of the system, as above;
2. `preprocessed_commit`, if not `null`;
3. the number of headers, then for each header: each entry of `active`,
   `stage_1_trace`, the number of `log_degrees`, each of them, the number of
   claims, and for each claim its length and its elements;
4. the number of messages, then for each message: the number of `args`, the
   `args`, the `multiplicity`;
5. sample beta, absorb beta, sample gamma, absorb gamma.

Each shard continues from a copy of the state reached there: it absorbs its
index `k`, then follows steps 8 to 14.

### `debug`

Values the verifier derives, for locating a mismatch. None of them is an
input. `fri_alpha`, `fri_betas` and `fri_indices` are `alpha`, `betas` and
`indices` of the `debug` object of `../fri/README.md`.

## What the generator checks

Every run asserts, for each vector:

* multi-stark's verifier (`verify_multiple_claims` or `verify_batch`) accepts
  the proof, and rejects it when one opened value is changed: one of stage 1,
  one of stage 2, one of the quotient, and one of the fixed traces if there
  are any; in a batch, in each shard.
* `seed`, recomputed from `params`, equals `config.challenger_seed()`, and the
  transcript replayed from `Challenger::from_hasher(seed, Blake3)` gives the
  same challenges as the one replayed from `config.initialise_challenger()`.
* A challenger whose initial state is `seed` followed by the bytes of
  everything absorbed before beta, written out by hand as the steps above
  state them (steps 1 to 6 of a single proof, 1 to 4 of a batch), gives the
  same challenges again.
* The transcript is replayed with multi-stark's public helpers, in the order
  above (`src/replay.rs`), and every challenge of `debug` is the one of an
  accepting run:
  * multi-stark's `verify_after_challenges` accepts when it is handed the
    replayed state with beta, gamma and the accumulator of the claims computed
    here, and rejects when any of the three is changed;
  * `zeta` is not zero, and the out-of-domain identity of every active
    circuit, recomputed with multi-stark's graph and lookup evaluators, holds
    with alpha and `zeta`, and fails when either is changed;
  * the grinding witnesses pass on the replayed challenger, and with
    `fri_alpha`, `fri_betas` and `fri_indices` every query folds down to the
    value of the final polynomial (`src/fri.rs`). The fold fails when
    `fri_alpha`, a beta or an index is changed, except for the beta of shard 1
    of `batch.json`, which has no effect, as noted under "Files".
* In a batch, the state reached by the replay is the one
  `System::batch_challenger` returns, and the residuals and the messages add
  up to zero.
* Each vector still has the features the table above lists for it
  (`check_coverage` in `src/main.rs`), and stays under 150 KB.
