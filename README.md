# certifri

A FRI polynomial commitment verifier in Lean 4, with a proof of soundness.
Only the verifier is certified. The prover is an ordinary Rust program.

The protocol is Plonky3's `TwoAdicFriPcs` at revision `3152b14a`, the revision
the Rust prover pins, with folding by two. The theorems are about the
commitment scheme and about the verifier of the STARK built on it, multi-stark
(`CertiFri/Stark/`): see
[The multi-stark verifier](#the-multi-stark-verifier). The protocol is not
zero-knowledge.

## Status

- **The verifier** is `Fri.verify` in `CertiFri/Verifier.lean`: executable,
  generic over the two fields, the two commitment schemes and the challenger,
  with no dependency beyond the Lean toolchain.
- **It is proved sound** in the random-oracle model, up to the unique-decoding
  radius, with no hypothesis about Reed–Solomon codes
  (`Exec.soundness_uniqueDecoding` in
  `Proofs/CertiFriProofs/Exec/SoundnessUnconditional.lean`), and from that
  **knowledge-sound** (`Exec.knowledge_soundness`) and **binding**
  (`Exec.binding`). It is also **complete** (`Exec.completeness`): it accepts
  every proof that follows the protocol, for any hash functions and any
  challenger. All on `propext`, `Classical.choice` and `Quot.sound`, with no
  `sorry`. The security theorems are about the verifier with ideal primitives;
  see [What the theorems assume](#what-the-theorems-assume).
- **It accepts proofs made by Plonky3**: with the Goldilocks, BLAKE3 and
  challenger code of `CertiFriP3`, it accepts the opening proofs that Plonky3
  produces and derives the same challenges, and it rejects tampered ones
  (`CertiFriTest/P3/Fri.lean`). This is a test on a handful of proofs, not a
  theorem. BLAKE3 and the challenger of `CertiFriP3` are tested against
  Plonky3, not proved.
- **The field arithmetic is proved.** The Goldilocks code on machine words and
  its quadratic extension implement a field of `p ^ 2` elements, with the
  structure the theorems need (`P3.Goldilocks.starkModel`), so the theorems
  hold over Goldilocks with nothing assumed about the arithmetic. The same is
  proved for BabyBear with its quartic extension and for the scalar field of
  BN254; see [The fields](#the-fields).
- **The multi-stark verifier** (`Stark.verify`, `Stark.verifyBatch` in
  `CertiFri/Stark/`) is a port of the STARK verifier that runs on this
  commitment scheme. It accepts proofs made by multi-stark and derives the
  same challenges (`CertiFriTest/Stark/MultiStark.lean`). **It is proved
  sound** in the random-oracle model (`Exec.Stark.soundness_verify_ud`,
  `Exec.Stark.soundness_verifyBatch_ud`): except with small probability, an
  accepted proof has committed columns that decode to base-field traces which
  satisfy every constraint on every row, and whose lookup messages are
  balanced. The theorems cover proofs of every trace height within stated size
  bounds. Over Goldilocks they are `P3.Goldilocks.soundness_verify` and
  `P3.Goldilocks.soundness_verifyBatch`; see
  [What is proved about it](#what-is-proved-about-it).
- **What remains** is listed in [TODO.md](TODO.md).

## The verifier

```lean
Fri.verify inputMmcs friMmcs chal init params shape commitments points values proof : Bool
```

The claims are given by a public shape and two flat arrays. The shape lists,
for each commitment, the matrices under it: the log of the row count, the
width, and the number of opening points. `points` holds the opening points in
the order batch, matrix, point, and `values` the claimed evaluations in the
order batch, matrix, point, column. `Fri.verifyClaims` (`CertiFri/Pcs.lean`)
takes the claims nested the way Plonky3's `pcs.verify` does.

The verifier absorbs the commitments, the opening points and the claimed values
into the challenger, and then follows Plonky3's `verify_fri`. Plonky3 leaves the
first two to the caller; a Plonky3 prover matches by observing the commitments
and the points before `pcs.open`.

It rejects a proof with a folding round of arity other than two.

## What is proved

`Proofs/CertiFriProofs/Exec/` relates the executable verifier to a model
verifier, and `Proofs/CertiFriProofs/Theory/` proves the model sound.

**Refinement** (`Exec.run_model_of_accepts`). If `Fri.verify` accepts, the model
verifier accepts the corresponding transcript. It has three parts: the
arithmetic of one query (`Exec/Arith.lean`), the commitment checks and the
verdict (`Exec/Checks.lean`), and the transcript (`Exec/Transcript.lean`).

**Soundness** (`Exec.soundness`). Fix the parameters and the shape of the
claims. An adversary making at most `Q` oracle queries gets the executable
verifier to accept claims that fail with probability at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|)

where `N` is `Q` plus the verifier's own queries, `εmax` bounds the error of
every round (divided by `2 ^ bits` where the round has a proof-of-work check),
and `D` is the digest type. "The claims fail" is about the functions that the
adversary's hash queries commit to under the commitments: at some height they
do not agree, on a `θ` fraction of the domain, with polynomials of the degree
bound that take the claimed values.

`Exec.soundness` takes two proximity hypotheses about Reed–Solomon codes, at
any agreement `θ`. `Exec.soundness_uniqueDecoding` proves both, for agreement
`θ = 1 - δ` with `2 * δ + ρ ≤ 1`, where `ρ = 2 ^ (-logBlowup)` is the rate:
every distance up to the unique-decoding radius. Its round errors are, with `n`
the log of the size of the first domain and `c = 2 ^ n * (δ * 2 ^ n + 1) + 1`,

- batching: `(number of claimed values) * c / |K|`,
- each folding round: `2 * c / |K| / 2 ^ commitPowBits`,
- queries: `(1 - δ) ^ numQueries / 2 ^ queryPowBits`,

for an extension field `K`, and `εmax` is their maximum.

For example, with blowup 4 the radius is `δ = 3/8`, so each query contributes
`log₂ (8/5) ≈ 0.68` bits: 100 queries give a query error of about `2 ^ -68`,
or `2 ^ -88` with 20 bits of proof of work. Over the quadratic extension of
Goldilocks (`|K| ≈ 2 ^ 128`), a trace of `2 ^ 20` rows (`n = 22`) with a
thousand claimed values has a batching error of about `2 ^ -75`, which is then
the largest of the three. These figures are arithmetic on the bound above, not
separate theorems.

**Knowledge soundness** (`Exec.knowledge_soundness`, `Exec/Extract.lean`).
`Exec.extractColumn` reads a polynomial for every committed column off the
commitments and the oracle query log, and nothing else: the function the hash
queries commit to under the commitment of the column's batch, decoded. The
probability that the verifier accepts while some claimed value is not the value
of the extracted polynomial at the opening point is at most the soundness
bound.

**Binding** (`Exec.binding`, `Exec/Binding.lean`). An adversary outputs two
statements with proofs, and both are verified. The probability that both are
accepted while they claim two different values for one column of the same
commitment at the same opening point is at most twice the soundness bound, with
the queries of both verifications counted.

Both need the extracted polynomial to be unique, which takes a margin inside
the radius: `2 * δ + ρ + 3 / n ≤ 1` at every level that has a claim, where `n`
is the size of that level's coset. The extracted polynomial has degree at most
the bound, one more than an honest polynomial. The extractor is a mathematical
choice read from the final log of the experiment: it is not computable as
defined, and its efficiency is not addressed.

**Completeness** (`Exec.completeness`, `Exec/Completeness.lean`). If the
statement is honest and the proof follows the protocol, `Fri.verify` returns
`true`. `Exec/Honest.lean` says what that means: behind the commitments are
polynomials of the allowed degree whose evaluations are the committed rows, the
claimed values are their values at the opening points, and, for the challenges
the verifier derives from the proof, each round commits to the fold of the
round before, the openings are the committed rows with Merkle paths that
verify, and the final polynomial is the last fold. `Merkle/Tree.lean` defines
the Merkle tree and proves that its openings verify. The hash functions and the
challenger are arbitrary: no random oracle is involved. Four conditions are
part of the statement: no opening point lies on the coset its matrix is
committed on; the proof-of-work witnesses pass; every field element has one
executable representation; the challenger returns indices of the first domain.

`Exec/HonestProver.lean` constructs such a proof: a prover, as a mathematical
function, that commits to each round after deriving the challenges of the
rounds before it. `Exec.completeness_honestProver`: for every honest statement
of a well-formed shape, the proof this prover builds is accepted, provided its
proof-of-work witness search succeeded.

The theory behind it:

| Module | Contents |
| --- | --- |
| `Theory/Basic` | Shared definitions: codewords, the fold, the proximity hypotheses, the query check. |
| `Theory/Domain` | Two-adic evaluation domains; query indices and domain points; cosets. |
| `Theory/Fold`, `Completeness` | Even and odd parts of a polynomial; honest codewords pass every query. |
| `Theory/Soundness`, `SoundnessCount` | Oracle-model soundness of the low-degree test, relative to the folding hypothesis. |
| `Theory/ProximityGap`, `StepMCA`, `Unconditional` | The proximity hypotheses proved by an elementary argument for `δ ≤ (1 - ρ) / (m + 1)` with `m` terms, and the low-degree test with no hypothesis under `4 * δ + ρ ≤ 1`. |
| `Theory/ProximityGap/UniqueDecoding`, `UniqueDecodingMCA` | The proximity hypotheses proved up to the unique-decoding radius `δ ≤ (1 - ρ) / 2`, for any number of terms: correlated agreement by the Berlekamp–Welch decoder with the challenge as an indeterminate, then the mutual form. |
| `Theory/Quotient`, `Pcs` | From the low-degree test to the evaluation claims. |
| `Theory/PcsRbr` | The whole check as one round-by-round sound protocol, with grinding. |
| `Theory/Oracle` | The random-oracle model: bad-event and collision bounds, Fiat–Shamir, Merkle binding and frozen trees against the query log. |
| `Theory/Compiled` | The model of the non-interactive protocol and its soundness. |
| `Theory/PcsRbr/Decode` | The polynomial a committed function decodes to, and that claims which hold are its evaluations. |
| `Theory/Compiled/TwoAttempts` | Soundness for two attempts on one oracle. |
| `Merkle/Tree` | The Merkle tree of a batch of matrices, and that the opening check accepts its openings. |
| `Exec` | The executable verifier refines the model; soundness of the executable verifier, with the proximity hypotheses and with them proved; knowledge soundness; binding; completeness. |

Also proved, about executable code: the Merkle opening check is binding up to a
hash collision (`CertiFri/Merkle.lean`), and Horner's rule computes the
evaluation of the final polynomial (`Proofs/CertiFriProofs/Poly.lean`).

### What the theorems assume

- **Ideal primitives.** The leaf hash, the compression function and the
  challenger are one random oracle. A row is hashed as the oracle's answer to
  the row of field elements it holds, and each challenge is the oracle's answer
  to everything the verifier has absorbed so far, in rounds
  (`Exec.freeChallenger`). The oracle answers the three kinds of query
  independently. Plonky3's BLAKE3 instantiation does not separate them: a leaf
  hash, a compression and a transcript hash are the same function on bytes.
- **Proximity gaps, beyond the unique-decoding radius only.** The theorems
  need two facts about Reed–Solomon codes, `CurveMCA` (batching the claims) and
  `StepMCA` (folding). Up to the unique-decoding radius, `2 * δ + ρ ≤ 1`, both
  are proved here and `Exec.soundness_uniqueDecoding` assumes nothing about
  the code. For a larger radius (towards the Johnson bound or capacity) they
  are hypotheses of `Exec.soundness`: arguments of the theorem, not axioms.
  The proved error is quadratic in the size of the domain.
- **The fields.** The two executable fields implement one mathematical field,
  every element of which is represented (`Exec.FieldModel`), the generator of
  the first domain is a primitive root of unity, and the coset shift is not
  zero (`Exec.WellFormed`). Both are proved for the Goldilocks code of
  `CertiFriP3` (`P3.Goldilocks.fieldModel`, `P3.Goldilocks.wellFormed`).
- **Merkle commitments with one path per query** (`merkleMmcs`).
- **A fixed shape.** The parameters and the shape of the claims are fixed
  before the adversary runs. The shape is not absorbed into the transcript.

### What they do not establish

- Anything about BLAKE3 or the challenger of `CertiFriP3`: that they are
  implemented correctly, or that they behave like a random oracle. The field
  arithmetic is proved ([The fields](#the-fields)).
- Soundness with Plonky3's pruned Merkle proofs as such. A pruned proof is
  unpacked and then checked by the certified Merkle check
  (`P3.prunedMmcs_accepts`), but the soundness theorem is stated for one path
  per query.
- That a proof-of-work witness exists: completeness assumes the search
  succeeded. Completeness with Plonky3's pruned Merkle proofs. Anything about
  the Rust prover: the honest prover of the completeness theorem is a
  mathematical definition.
- An efficient extractor, binding for two openings of different shapes, and
  knowledge soundness or binding for columns on cosets too small for the
  margin above.
- Zero knowledge. The protocol is not zero-knowledge.
- That the verifier accepts exactly what Plonky3's accepts. The tests compare
  the two on a few proofs.
- The honest degree bound: an accepted claim is about a polynomial of degree at
  most the bound, one more than an honest polynomial has, and agreement is not
  asked at the claim's own opening point. The committed functions take values
  in the extension field.

## The multi-stark verifier

`CertiFri/Stark/` is a port of the verifier of
[multi-stark](https://github.com/argumentcomputer/multi-stark) at revision
`3515632`: a STARK for systems of several circuits connected by lookups, over
Plonky3's FRI.

```lean
Stark.verify      inputMmcs friMmcs chal init sys claims proof : Bool   -- System::verify_multiple_claims
Stark.verifyBatch inputMmcs friMmcs chal init sys batch        : Bool   -- System::verify_batch
```

`sys` is the verifying key: for each circuit its constraint graph, its lookups
and its widths, the commitment to the fixed traces, and the parameters. The
verifier checks the shape of the proof, derives the lookup challenges, the
constraint challenge and the out-of-domain point with the challenger, checks
the opened values with `Fri.verifyFrom` (the FRI verifier above, started from
the challenger state the STARK transcript reaches, as Plonky3's `pcs.verify`
is), and evaluates the constraints of every active circuit, the logUp
constraints among them, on the opened values.

| File | Content |
| --- | --- |
| `Stark/Graph.lean` | Constraint graphs and their evaluation |
| `Stark/Logup.lean` | The values of the lookup constraints, in coordinates of the extension |
| `Stark/System.lean` | Systems, proofs, batch preambles |
| `Stark/Verifier.lean` | The shape check, the transcript, the opening claims, the constraint check, `verify`, `verifyBatch` |

### What is proved about it

The theorems are in `Proofs/CertiFriProofs/Exec/Stark/`, over the algebra in
`Proofs/CertiFriProofs/Theory/Stark/`. All are on `propext`, `Classical.choice`
and `Quot.sound`, with no `sorry`.

**The experiment.** The system (the verifying key) is fixed. An adversary with
`Q` queries to a random oracle outputs public claims and a proof, or a batch.
Then the queries of the verification are made. One oracle answers the
challenge queries of the Fiat–Shamir chains and the hash queries of the Merkle
trees.

**Soundness** (`soundness_verify_ud`, `soundness_verifyBatch_ud` in
`Unconditional.lean`). Let `δ ≥ 0` with `2 * δ + 2 ^ (-logBlowup) < 1`. The
probability of the following event is at most
`N * starkErr + ((S + 1) * r + 3) * N * (N - 1) / (2 * |D|)`: some answer
function that agrees with the final log makes the verifier accept a proof
within the size bounds (`Covered`), and some constraint value of some active circuit (a zero of its graph,
or a lookup constraint) is not zero on some row of its trace domain. The
constraint values are those of the polynomials that the committed columns
decode to, at agreement `1 - δ`, against the log; they are functions of the
commitments and the oracle queries alone.

`N` is the number of oracle queries of the experiment, `S` the bound on the
number of shards, `r` the largest number of rounds of a chain and `|D|` the
number of digests. `starkErr` is the largest error of a round:

| Round | Error |
| --- | --- |
| lookup challenge `β` | `2 * itemBound / \|K\|` |
| lookup challenge `γ` | `2 * itemBound * lenBound / \|K\|` |
| constraint challenge `α` | `(constraintBound - 1) / \|K\|` |
| out-of-domain point `ζ` | `(zetaBound + cosetBound) / \|K\|` |
| opening proof, batching | `valueBound * c / \|K\|` |
| opening proof, each folding round | `2 * c / \|K\| / 2 ^ commitPowBits` |
| opening proof, queries | `(1 - δ) ^ numQueries / 2 ^ queryPowBits` |

Here `c = 2 ^ n * (δ * 2 ^ n + 1) + 1` with `n = maxLogDegree + logBlowup`;
`itemBound` bounds the number of lookup messages and `lenBound` their length,
`constraintBound` is the largest number of constraint values of a circuit,
`zetaBound` the degree of the polynomial checked at `ζ`, `cosetBound` the
number of points `ζ` at which an opening point falls in a committed coset, and
`valueBound` the number of opened values.

The columns are decoded with no slack (`decodeT` in
`Theory/PcsRbr/DecodeTight.lean`): inside the unique-decoding radius, which is
what `2 * δ + 2 ^ (-logBlowup) < 1` says, a word has at most one polynomial at
agreement `1 - δ`, whatever the height of the trace. The opening proof only
guarantees agreement away from an opening point that lies in the committed
coset; the `cosetBound` term pays for the points `ζ` where that can happen.

**What the conclusion means** (`Meaning.lean`, `Lookups.lean`,
`Theory/Stark/BalanceInt.lean`).

- If the zeros of a circuit read only the fixed and the main traces
  (`Circuit.ZerosPlain`), every one of them holds on every row, on the values
  of the decoded fixed and main columns (`zeros_of_not_constraintFail`). These
  columns have base-field coefficients (`coeff_shardCols_mem_base`).
- If the lookups of every circuit read only the fixed and the main traces
  (`Circuit.LookupsPlain`; the zeros may read anything), the lookup messages of
  an accepted proof are balanced (`soundness_verify_lookups_ud`,
  `soundness_verifyBatch_lookups_ud`, with the same bound): the public claims,
  what every circuit sends on every row of its trace, and the messages of a
  batch are such that, for every message, its multiplicities add up to zero in
  the field. multi-stark compiles the lookups of a circuit first and without
  the lookup trace, so its systems meet the condition once public values are
  kept out of lookups.
- Balanced in the field is balanced over the integers when the multiplicities
  are integers whose absolute values add up to less than the characteristic
  (`balanced_int_of_balanced`); for multiplicities `1` and `-1`, the multiset
  of sent messages is then the multiset of received ones
  (`map_fpPoly_eq_of_balanced`). That the multiplicities of a circuit are such
  integers is not proved here.

**On the way.** The state function of the protocol and its round-by-round
soundness (`rbrSound_sdoomed` in `State.lean`); the injectivity of the
transcript encoding of both entry points (`Encode.lean`); the round-by-round
soundness of the opening protocol for every supported shape, with one error
bound (`PcsSound.lean`); the refinement of the executable checks
(`Arith.lean`, `Run.lean`).

### What these theorems assume

- **The random-oracle model with ideal primitives**, as for the commitment
  scheme. The challenger is idealised (`uChallenger`): the field challenge, the
  proof-of-work bits and the query indices of a round are independent parts of
  one uniform answer of the oracle to everything absorbed so far. Merkle trees
  hash with the same oracle.
- **`StarkModel`**: the executable fields implement a field, with the
  extension basis and coordinates the verifier uses, and compatible two-adic
  generators that are primitive roots. These laws are proved for the
  Goldilocks code of `CertiFriP3` (`P3.Goldilocks.starkModel`), and the four
  theorems are restated over Goldilocks without this assumption
  (`Proofs/CertiFriProofs/P3/GoldilocksSoundness.lean`).
- **A system fixed before the adversary runs.** The transcript absorbs the
  sizes of the circuits, not their constraint graphs.
- **A well-formed system**: a circuit without a fixed trace has fixed-trace
  width zero (`System.FixedOk`), no fixed trace is taller than the largest
  trace the system supports (`System.HeightOk`), and that largest trace exists
  in the field.
- **`Covered`**, the only condition on the proof the event is about: the
  numbers of shards, public claims and messages, and their lengths, are within
  bounds. The bounds enter the errors, and all sizes are below the
  characteristic. There is no condition on the shape of the proof or on the
  heights of its traces: what the theorems need of them follows from
  acceptance.
- For the meaning of the conclusion: `Circuit.ZerosPlain` or
  `Circuit.LookupsPlain` as above, and a characteristic other than two.

### What they do not establish

- What the constraints mean for a particular system, and any policy on claims
  and messages (ix's `validate_preamble` is not part of multi-stark and not
  modelled). "Balanced" is in the field: multiplicities are field elements, and
  two messages that differ by trailing zeros are the same message.
- Anything about proofs that are not covered: more shards, claims or messages
  than the bounds.
- Completeness of the STARK verifier, which is tested on proofs made by
  multi-stark and not proved. Zero knowledge.
- The exact degree: a decoded column has degree at most `2 ^ k`, one more than
  an honest column of a trace of `2 ^ k` rows.
- The Plonky3 instantiation, as for the commitment scheme.

## The fields

The theorems hold for any executable fields that implement a mathematical
field with the structure the verifier uses (`FieldModel`, `StarkModel`). For
the fields of `CertiFriP3` this is proved, in `Proofs/CertiFriProofs/P3/`.

| Field | Code | Model |
| --- | --- | --- |
| Goldilocks, `p = 2^64 - 2^32 + 1` | `Goldilocks.lean`, on 64-bit words | `ZMod p` |
| its quadratic extension | `GoldilocksExt.lean` | `(ZMod p)[X] / (X^2 - 7)`, `p ^ 2` elements |
| BabyBear, `p = 2^31 - 2^27 + 1` | `BabyBear.lean`, on natural numbers | `ZMod p` |
| its quartic extension | `Quartic.lean` | `(ZMod p)[X] / (X^4 - 11)`, `p ^ 4` elements |
| the scalar field of BN254 | `Bn254.lean`, on natural numbers | `ZMod r` |

For each of them:

- **The order is prime** (`Primes.lean`), by Lucas's test on a factorisation
  of `p - 1`, with the modular powers evaluated by Lean's kernel. For BN254
  the two large prime factors of `r - 1` have their own certificates.
- **Each operation of the code is the field operation.** For Goldilocks this
  is a proof about machine words (`GoldilocksWord.lean`): sums and differences
  with one correction, the product through a 128-bit value reduced with
  `2^64 = 2^32 - 1` and `2^96 = -1` modulo `p`, and the inverse by the extended
  Euclidean algorithm. BabyBear and BN254 share one implementation on natural
  numbers (`CertiFriP3/PrimeField.lean`, proved in `FpLaws.lean`), whose
  inverse is a power, by Fermat's little theorem.
- **The extension is a field**: `X^2 - 7` is irreducible over Goldilocks and
  `X^4 - 11` over BabyBear (`Binomial.lean`, `Primes.lean`), and the code of
  the extension computes in the quotient (`GoldilocksModel.lean`,
  `QuarticLaws.lean`), inverses included.
- **The generators of the two-adic subgroups are primitive roots of unity**
  of their orders: each entry of Plonky3's table is the square of the next,
  checked by evaluating the code, and the entry of order two is `-1`.

The results are `P3.Goldilocks.starkModel` and `P3.BabyBear.starkModel`, the
models the theorems assume, and `P3.Bn254.refines` with
`P3.Bn254.isPrimitiveRoot_twoAdicGenerator`. A new field needs three facts
(`PrimeRep`, `TwoAdicRep`, `BinomialRep` in `PrimeRep.lean` and `Model.lean`),
from which `P3.starkModel` builds the model.

Not proved: the encodings of field elements as bytes, which the hashers and
the challenger use. BabyBear has no hasher and no challenger in this
repository, so no verifier runs over it end to end; the scalar field of BN254
is there for the field alone.

## Tests

They run as part of the build: a failing `#guard` fails the build.

- `CertiFriTest/Fri.lean`: an honest prover over the field with 97 elements,
  written as test code, with a toy hasher and a toy challenger. The verifier
  accepts its proofs and rejects tampered ones.
- `CertiFriTest/P3/Fri.lean`: the verifier on four opening proofs made by
  Plonky3 (`CertiFriTest/vectors/fri`, a Rust program that also checks each
  proof with Plonky3's verifier). Each is accepted with one Merkle path per
  query and with Plonky3's pruned proofs, the derived challenges equal
  Plonky3's, and tampered values, points, final polynomials, sibling values,
  opened entries, witnesses and parameters are rejected.
- `CertiFriTest/P3/`: Goldilocks, its quadratic extension, BLAKE3, the Merkle
  hashers, the challenger and the pruned Merkle proofs against values computed
  by Plonky3. BabyBear, its quartic extension and the scalar field of BN254
  against natural-number arithmetic and against values computed by Plonky3 at
  revision `0d803737` (`CertiFriTest/vectors/fields`).
- `CertiFriTest/Merkle.lean`: the Merkle tree layout against openings produced
  by Plonky3.
- `CertiFriTest/Stark/MultiStark.lean`: `Stark.verify` on three proofs and
  `Stark.verifyBatch` on a batch of two shards, all made by multi-stark in its
  production configuration (`CertiFriTest/vectors/stark`, a Rust program that
  also checks each proof with multi-stark's verifier). Between them the
  systems have circuits of different heights, fixed traces, an inactive
  circuit with and without a fixed trace, lookups in groups, extension
  constraints and quotients of up to four chunks. Each proof is accepted, the
  derived challenges equal multi-stark's, and changed opened values,
  accumulators, commitments, bitmaps, claims, messages, constraints and
  parameters are rejected. `CertiFriTest/Stark/Arith.lean` checks the
  coordinate arithmetic of the lookup constraints.

The JSON format of the vectors is this repository's own. Decoding the bytes a
Plonky3 prover serializes is not written.

## Benchmark

```sh
(cd CertiFriTest/vectors/fri && cargo run --release -- --bench /tmp/bench 200)  # Plonky3's verifier
lake exe certifri-bench /tmp/bench/bench-16.json 50                             # this verifier, compiled
```

Both verify the same proofs (blowup 4, 100 queries, 16 bits of grinding), on
one thread, without the time to decode the proof. On the machine these were
last run on (AMD Ryzen 7 8845HS), per verification:

| First domain | Plonky3 | This verifier, one path per query | This verifier, pruned proofs |
| --- | --- | --- | --- |
| `2^12` | 1.3 ms | 3.9 ms | 4.9 ms |
| `2^16` | 2.2 ms | 5.8 ms | 8.0 ms |
| `2^20` | 3.2 ms | 7.4 ms | 10.3 ms |

Plonky3 verifies pruned proofs, so the last column is the like-for-like one.
More than half of this verifier's time with one path per query is the
arithmetic of the queries, which inverts one extension-field element per
claimed value; Plonky3 inverts one per opening point, in a batch.

## Layout

| Path | Contents |
| --- | --- |
| `CertiFri/` | The certified FRI verifier, and the port of the multi-stark verifier (`Stark/`). No dependency beyond the Lean toolchain. Proofs that need only core Lean sit next to the code. |
| `CertiFriP3/` | The Plonky3 instantiation: the fields (Goldilocks, BabyBear, the scalar field of BN254, and extensions), BLAKE3, the challenger, pruned Merkle proofs. The fields are proved in `Proofs/CertiFriProofs/P3/`; the rest is tested. |
| `CertiFriTest/` | Executable checks against reference code and against Plonky3, and the generators of their vectors. |
| `Proofs/` | A separate Lake package that depends on Mathlib and on `CertiFri`: the security theory, and the refinement of the executable verifier to it. |
| `plonky3/` | Submodule: a Plonky3 checkout for reference. Nothing builds from it. |

Mathlib is confined to `Proofs/` so that a project can depend on the verifier
without inheriting it.

`CertiFri/Schedule.lean` and `CertiFri/Shape.lean` derive a folding schedule
from the claims, as later Plonky3 revisions do, and prove two properties of it.
The verifier does not use them: at revision `3152b14a` the arities are read
from the proof, and the verifier requires each to be two. The `plonky3/`
submodule points at that later revision (`0d803737`), not at `3152b14a`.

## Build

```sh
lake build --wfail                 # the verifier, the Plonky3 instantiation, the tests
(cd Proofs && lake build --wfail)  # the proofs; fetches Mathlib on first use
```

`--wfail` turns warnings into errors, so a `sorry` fails the build.
The two `lean-toolchain` files must name the same toolchain.
