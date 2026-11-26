# What remains

What is certified today: the Lean verifiers `Fri.verify`, `Stark.verify` and
`Stark.verifyBatch` are proved sound in the random-oracle model, over
Goldilocks and its quadratic extension, with nothing assumed about the field
arithmetic. The [README](README.md) states the theorems and their assumptions.

This file lists what stands between those theorems and "a proof accepted in
production is a proof of the statement". Each item says where the gap shows in
the code and what closing it takes. The order within a section is by how much
the item matters.

## 1. Between the theorems and the verifier that runs

- [ ] **The Rust verifier of multi-stark is not the Lean verifier.** The two
  are connected by tests only: the Lean verifier accepts four proofs made by
  multi-stark, derives the same challenges, and rejects tampered ones
  (`CertiFriTest/Stark/MultiStark.lean`). Nothing is proved about the Rust
  code. To close: run the compiled Lean verifier as the check, or as a second
  check, in production; the trusted base is then the Lean compiler and
  runtime. Short of that, compare the two verifiers on many more proofs,
  including malformed ones. That is evidence, not a proof.
- [ ] **ix's `validate_preamble` is not modelled.** The theorems say that the
  lookup messages of a batch are balanced. What the claims and messages mean,
  and which ones ix admits, is decided by `validate_preamble`, which is not
  part of multi-stark. To close: port it, and state what an accepted batch
  says about ix's messages.
- [ ] **The port is a restriction of multi-stark** (`CertiFri/Stark/Verifier.lean`,
  "Differences from multi-stark"): the two `omit_*` options are off, the
  opening proof folds by two only, and the theorems are stated for one Merkle
  path per query (a pruned proof of Plonky3 is unpacked and then checked,
  `P3.prunedMmcs_accepts`). The configuration ix ships is outside the
  restriction: multi-stark v6 batches the opening claims with tensor weights
  (`FriBatching::Tensor`, which ix's keys require), while the port and every
  theorem here batch by powers of one challenge; v6 also absorbs the extension
  degree, a modulus tag and the verifying-key digest into its transcript and
  works over the cubic extension of Goldilocks, for which there is no
  `StarkModel`. No theorem here covers a v6 proof. `CertiFri/TensorBatching.lean`
  and `Exec/SoundnessTensor.lean` hold the tensor weights and a proximity
  property of them (`Tensor2DMCA`), which no verifier and no soundness theorem
  uses.
- [ ] **There is no decoder for multi-stark's proof format.** The tests read
  proofs from JSON files written by Rust programs of this repository
  (`CertiFriTest/vectors`). Running the Lean verifier on production proofs
  needs a decoder of multi-stark's serialisation, for the proof and for the
  public claims. A bug in decoding the proof can only make the verifier
  reject, since soundness holds for whatever proof object comes out; a bug in
  decoding the claims or the system changes the statement.

## 2. Ideal primitives

The security theorems are about the verifier run with ideal primitives. The
hash function being a random oracle is a standard assumption and stays one.
The rest of this section can be proved.

- [ ] **The hashers.** The model hashes a row as the oracle's answer to the row
  of its values in the field (`inputHasher`, `friHasher`). The code hashes
  bytes (`CertiFriP3/Hashers.lean`). Missing: the byte encoding of a row and of
  a pair of digests is injective, and the encodings of leaves and of inner
  nodes cannot collide. With that, BLAKE3 as a random oracle on bytes gives
  the ideal hashers. This needs the byte encoding of a field element
  (`Goldilocks.pushBytes`, `Goldilocks.ofCanonical?`) to be injective, which
  is not proved either.
- [ ] **The challenger.** The model's challenger (`uChallenger`) returns
  independent uniform challenges, proof-of-work bits and query indices as one
  answer of the oracle to everything absorbed so far. The code
  (`CertiFriP3/Challenger.lean`) is Plonky3's
  `SerializingChallenger64<Goldilocks, HashChallenger<u8, Blake3, 32>>`: a hash
  chain over bytes with nothing added to delimit the values, field elements by
  rejection sampling of 64-bit words (cut off after a fixed number of
  rejections), bits and indices from the low bits of a word. Missing: a
  theorem that the second is close to the first when BLAKE3 is a random
  oracle, with the distance as an explicit term, and that what is absorbed
  determines the messages (the encoding of the transcript is injective for the
  model's messages, `Exec/Stark/Encode.lean`, but not proved for the bytes).
- [ ] **BLAKE3** (`CertiFriP3/Blake3.lean`) is tested against reference
  vectors here. ix proves the plain hash equal to the specification
  `Blake3.Pure.digest` (`blake3_eq_pure`, ix's
  `Ix/Cert/MultiStark/Blake3Parity.lean`). The keyed `derive_key` modes that
  multi-stark v6 hashes with (`CertiFriP3/DomainSep.lean`) have no such
  theorem: their context keys are kernel-checked, and they are tested against
  vectors.

## 3. The statement of soundness

- [ ] **The proved error is for the unique-decoding radius.** The parameters
  of multi-stark's v5 configuration (blowup 4, 100 queries, 20 proof-of-work
  bits; ix's v6 default has 128 queries) are chosen for the conjectured
  security of FRI; inside the unique-decoding radius the proved
  query error is about `2 ^ -88`, and the batching error is larger (README,
  "What is proved"). For the opening
  proof alone, a larger radius can be supplied as a hypothesis about
  Reed–Solomon codes (`Exec.soundness`). For the STARK the columns are defined
  by unique decoding (`decodeT`), so a larger radius needs a different
  argument (list decoding, with a term for the number of codewords).
- [ ] **The system is fixed before the adversary runs.** The transcript
  absorbs the sizes of the circuits, not their constraint graphs. For a
  verifying key fixed in advance this is the right statement; an adversary
  that chooses the system after seeing the oracle is not covered.
- [ ] **Balance is in the field.** The theorems give balance of the lookup
  messages with multiplicities in the field, up to trailing zeros. Balance
  over the integers follows when the multiplicities are integers whose
  absolute values add up to less than the characteristic
  (`Theory/Stark/BalanceInt.lean`). That a circuit's multiplicities are such
  integers is not proved for any circuit.
- [ ] **`Circuit.LookupsPlain` has no executable check.** The lookup theorems
  assume that the lookups of every circuit read only the main and fixed traces
  and the selectors of multi-stark's compiler (`Exec/Stark/Meaning.lean`). It
  is a proposition about the system. Missing: a function that checks it, with
  a proof that the check implies the proposition, so that it can be run on a
  system.
- [ ] **Size bounds.** The theorems are about proofs with at most a stated
  number of shards, claims and messages (`Covered`, `BatchCovered`); the
  bounds enter the error.
- [ ] **The exact degree.** A decoded column has degree at most `2 ^ k`, one
  more than an honest column of a trace of `2 ^ k` rows.
- [ ] **No efficient extractor.** The traces of the conclusion are decoded
  from the oracle's log by a mathematical definition, not by an algorithm
  with a stated running time.

## 4. Completeness

- [ ] **Completeness of the STARK verifier is not proved.** That honest proofs
  are accepted is tested on proofs made by multi-stark. A theorem needs a
  model of the honest prover (traces, their low-degree extensions, the lookup
  traces, the quotient, the openings), as `Exec.completeness` has for the
  opening proof. This is the theorem that would have caught the selector
  values in lookups (section 6): an honest proof that the verifier rejects.
- [ ] **Completeness of the opening proof** assumes that the search for a
  proof-of-work witness succeeded, and is stated for one Merkle path per
  query, not for pruned proofs.

## 5. Fields

Proved (`Proofs/CertiFriProofs/P3/`): Goldilocks on machine words and its
quadratic extension; BabyBear and its quartic extension; the scalar field of
BN254. Each order is proved prime, each operation is the field operation, and
the generators of the two-adic subgroups are primitive roots.

- [ ] **Byte encodings of field elements**: see section 2.
- [ ] **BabyBear has no hasher and no challenger here.** multi-stark's
  BabyBear configuration hashes with Poseidon2 and uses a duplex challenger;
  neither is in `CertiFriP3`. The field laws are proved, but no verifier runs
  over BabyBear end to end.
- [ ] **BN254 is a field only.** The scalar field is the one ix's compression
  pipeline computes in. The base field of the curve, the curve, the pairing
  and the KZG, PLONK and Groth16 verifiers are not in this repository
  (section 7).
- [ ] **Other fields of Plonky3.** KoalaBear and its quartic extension would be
  another instance of `Fp` and `Quartic` (`W = 3`), with a primality proof of
  the order. Mersenne31 has no two-adic subgroups and needs the circle
  version of the protocol, which is not here.

## 6. Upstream

- [ ] **multi-stark, branch `gb/lookup-selector-fix`** (two commits, not
  merged): public values and the three row selectors are compile errors in
  lookup expressions. Without the second, a system that uses a selector in a
  lookup has honest proofs that the verifier rejects. When ix moves to that
  branch, two tests of `crates/proof-compression` that put selectors in
  lookups need indicator columns instead.
- [ ] **Graphs that are not built by multi-stark's `compile`** (a deserialised
  key, ix's `stark-key` decoder) bypass both compile errors. They need the
  same check when they are loaded.

## 7. Outside this repository

- [ ] **What the constraints mean.** The theorems say that the committed
  traces satisfy the constraints of the system. That the constraints of an
  Aiur program say what the program computes is a statement about ix's
  compiler from Aiur to multi-stark.
- [ ] **The compression pipeline.** ix compresses a multi-stark proof through
  KZG, PLONK or Groth16 over BN254. None of those verifiers is modelled.
- [ ] **The verifier written in Aiur** is a third copy of the multi-stark
  verifier. It is out of scope by decision.
- **Zero knowledge** is out of scope by decision: the protocol is not
  zero-knowledge. multi-stark's v6-zk mode is not modelled: no theorem here
  states hiding, and the `…_v6Zk_soundness_…` theorems of
  `Exec/SoundnessZk.lean` are the soundness theorems of the unsalted,
  Horner-batched `Fri.verify`.
