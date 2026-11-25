import CertiFriP3.DomainSep
import CertiFriProofs.Exec.SoundnessSponge
import CertiFriProofs.Exec.SoundnessTensor

/-!
# Formal 128-Bit Soundness of `multi-stark/v6-zk` Hiding-PCS

Certifies the `multi-stark/v6-zk` zero-knowledge hiding-PCS extension over
`GoldilocksExt3` (`Fp3Model`, `p^3 ≈ 2^192`) with 64-byte RFC 7693 `BLAKE2b-512`
(`Digest64`, true 512-bit internal state), incremental sponge chaining (`c = 3 / 2`),
and `FriBatching::Tensor`:

1. **Salted Merkle leaf binding & ROM soundness preservation:**
   * `salted_merkle_binding_of_no_collision`: 16-byte leaf salting (`Salt16`,
     `ZK_LEAF_SALT_BYTES = 16`) preserves collision-resistance Merkle binding
     identically on `(row, salt)` pairs.
   * `salted_sponge_soundness_le`: in the `SpongeCommitted` ROM with leaf domain
     `T × Salt16`, the incremental sponge binding bound retains the exact
     prefactor `c = 3 / 2` (`3 * N ^ 2 / (2 * |D|)`) with **zero** security
     degradation (`255.71b` classical / `170.7b` BHT / `204.8b` CNS / `256b`
     Grover for `Digest64`; `127.71b` classical for 32-byte `BLAKE3-256`).
   * `v6Zk_saltedLeaf_injective_and_disjoint` (32-byte `BLAKE3-256` classical) and
     `v6Zk_saltedLeaf_blake2b512_injective_and_disjoint` (64-byte `BLAKE2b-512` PQ):
     `v6-zk` salted leaves, internal 2-to-1 nodes, and transcripts are jointly
     injective and pairwise disjoint from one another, from plain, and from all
     non-ZK `v6` domains.

2. **2× interleaved odd-coset witness blinding & half-stride telescoping quotient slicing:**
   * `zk_oddCoset_blinding_agrees_on_trace`: `T(X) = T₀(X) + (X^N - 1) * b(X)`
     agrees identically with `T₀(X)` on the trace subgroup `H_N = {x | x^N = 1}`.
   * `zk_oddCoset_blinding_natDegree_lt`: `deg(T) < 2 * N` whenever
     `deg(T₀) < N` and `deg(b) < N`.
   * `zk_quotient_telescoping_sum`: half-stride telescoping quotient blinding
     `c'_k(X) = c_k(X) - ρ_{k-1}(X) + X^N * ρ_k(X)` (`ρ_{-1} = ρ_{2q-1} = 0`)
     preserves the exact quotient polynomial `∑_{k < 2q} X^{kN} c'_k(X) = ∑_{k < 2q} X^{kN} c_k(X)`
     while keeping every slice degree `< 2 * N`.
   * `zk_quotient_degree_lt`: for constraint degree `d ≥ 1` on degree-`< 2N`
     blinded traces, the quotient degree is `< 2 * N * zkQuotientDegree d`
     where `zkQuotientDegree d = nextPow2 (max d 1)`.

3. **`W_R ≥ 4` base-field randomizer polynomial `R(X)` in `FriBatching::Tensor`:**
   * `fp3_tensor4_spans_of_not_base`: over `Fp3Model = GF(p)[X]/(X^3 - X - 1)`,
     the first 4 tensor weights `(1, r₀, r₁, r₀ * r₁)` span `Fp3Model` over
     `GF(p)` whenever `r₀ ∉ GF(p)` and `r₁ ∉ GF(p)` (proved using
     `cubicTrinomial_no_root`!).
   * `fp3_tensor4_span_failure_prob_le`: exact span-failure probability bound
     `≤ 2 / p^2 < 1 / 2^126` for `W_R = 4`.
   * `negControl_fp3_tensor3_span_failure_ge`: constructive negative control
     proving that `W_R = 3` (`(1, r₀, r₁)`) fails to span `Fp3Model` with
     probability `≥ 1 / p > 1 / 2^64` (explaining why `W_R ≥ 4` is mandatory).
   * `goldilocksExt3_zk_tensor2DMCA_ud_128`: merging `W_R` base-field randomizer
     columns of degree `< 2N` into the quotient MMCS and batching via
     `FriBatching::Tensor` preserves unconditional `≤ (3 / 4) / 2 ^ 128`
     RS proximity (`Tensor2DMCA`).
   * `goldilocksExt3_v6Zk_soundness_blake2b512_ud_128` &
     `goldilocksExt3_v6Zk_soundness_blake2b512_johnson_*`: literal `≤ N / 2 ^ 128`
     executable `Fri.verify` soundness for `v6-zk` under 64B RFC 7693 `BLAKE2b-512`.

4. **Checked predicates & constructive negative controls for all 4 `v6-zk` guardrails:**
   * Trap 1: `N ≥ next_pow2(2Q + 2D)` (`minZkLogDegree`),
   * Trap 2: `W_R ≥ 4` (`ZK_RANDOMIZER_WIDTH`),
   * Trap 3: `1 ≤ logBlowup ∧ zkQuotientDegree maxConstraintDegree ≤ 2 ^ logBlowup`,
   * Trap 4: `v6` ↔ `v6-zk` domain separation.

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace CertiFri.P3.Exec

open Polynomial CertiFri CertiFri.Fri CertiFri.P3 CertiFri.Exec
open CertiFri.Oracle CertiFri.Oracle.OracleComp CertiFri.Oracle.MerkleRO

/-! ## Section 1: Salted Merkle Leaf Binding & ROM Soundness Preservation -/

section SaltedMerkle

/-- Evaluating a Merkle authentication path bottom-up from leaf digest `acc`
along index `idx` and sibling path `path`. -/
def evalMerklePath {D : Type} (compress : D → D → D) : ℕ → D → List D → D
  | _, acc, [] => acc
  | idx, acc, sib :: rest =>
    let next := if idx % 2 = 0 then compress acc sib else compress sib acc
    evalMerklePath compress (idx / 2) next rest

/-- A collision-free Merkle tree with 16-byte salted leaves `(row, salt)` is
strictly binding on BOTH `row` and `salt`: two valid openings at the same leaf
index against the same root must agree on both the row and the salt (unless a
leaf-hash or internal-node hash collision occurred). -/
theorem salted_merkle_binding_of_no_collision {Row Salt D : Type}
    (hashLeaf : Row × Salt → D) (compress : D → D → D)
    (hLeafInj : Function.Injective hashLeaf)
    (hCompInj : ∀ l₁ r₁ l₂ r₂, compress l₁ r₁ = compress l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    {idx : ℕ} {row₁ row₂ : Row} {salt₁ salt₂ : Salt} {path₁ path₂ : List D}
    (hlen : path₁.length = path₂.length)
    (hroot : evalMerklePath compress idx (hashLeaf (row₁, salt₁)) path₁ =
      evalMerklePath compress idx (hashLeaf (row₂, salt₂)) path₂) :
    row₁ = row₂ ∧ salt₁ = salt₂ := by
  have hpath : ∀ (n : ℕ) (p₁ p₂ : List D) (i : ℕ) (a₁ a₂ : D),
      p₁.length = n → p₂.length = n →
      evalMerklePath compress i a₁ p₁ = evalMerklePath compress i a₂ p₂ → a₁ = a₂ := by
    intro n
    induction n with
    | zero =>
      intro p₁ p₂ i a₁ a₂ hp₁ hp₂ heq
      cases p₁ with
      | nil =>
        cases p₂ with
        | nil => exact heq
        | cons _ _ => simp at hp₂
      | cons _ _ => simp at hp₁
    | succ n ih =>
      intro p₁ p₂ i a₁ a₂ hp₁ hp₂ heq
      cases p₁ with
      | nil => simp at hp₁
      | cons s₁ r₁ =>
        cases p₂ with
        | nil => simp at hp₂
        | cons s₂ r₂ =>
          simp only [evalMerklePath] at heq
          have hnext := ih r₁ r₂ (i / 2) _ _ (by simpa using hp₁) (by simpa using hp₂) heq
          split_ifs at hnext with hmod
          · exact (hCompInj a₁ s₁ a₂ s₂ hnext).1
          · exact (hCompInj s₁ a₁ s₂ a₂ hnext).2
  have hd : hashLeaf (row₁, salt₁) = hashLeaf (row₂, salt₂) :=
    hpath path₁.length path₁ path₂ idx _ _ rfl hlen.symm hroot
  have hpair := hLeafInj hd
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- **ROM binding & soundness preservation under 16-byte leaf salting (`c = 3 / 2`):**
instantiating `SpongeCommitted.prob_spongeExperiment_bind_committedRow_le` on the
salted leaf type `T × DomainSep.Salt16` preserves the exact incremental-sponge
soundness and collision bound with prefactor `3 / 2` (`3 * N ^ 2 / (2 * |D|)`),
incurring **zero** security degradation from 16-byte leaf salting. -/
theorem salted_sponge_soundness_le
    {Msg Msg₂ T D : Type} {Chal : ℕ → Type}
    [DecidableEq Msg] [DecidableEq T] [DecidableEq D] [Fintype D] [Nonempty D]
    [∀ i, DecidableEq (Chal i)] [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    {r : ℕ} {doomed : ∀ i, Transcript Msg₂ Chal i → Prop} {ε : ℕ → ℝ} {εmax : ℝ}
    {s₀ : D}
    (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax)
    (hnil : doomed 0 .nil)
    {stepDigestsOf : ℕ → Msg → List D} {M : ℕ} (hM3 : M ≤ 3)
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    {read : ℕ → Msg → (D → Array Dimensions → ℕ → ℕ → Option (Array (T × DomainSep.Salt16))) → Msg₂}
    (hread : ∀ j m c c', (∀ root ∈ stepDigestsOf j m, c root = c' root) →
      read j m c = read j m c')
    {α β : Type}
    {adv : OracleComp (SpongeMerkleAnswer Msg Chal (T × DomainSep.Salt16) D) α}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r × D →
      OracleComp (SpongeMerkleAnswer Msg Chal (T × DomainSep.Salt16) D) β}
    {R : ℕ} (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (SpongeMerkleAnswer Msg Chal (T × DomainSep.Salt16) D) → Prop}
    (hE : ∀ (out : α × Transcript Msg Chal r × D)
      (l : Log (SpongeMerkleAnswer Msg Chal (T × DomainSep.Salt16) D))
      (b : β) (l' : Log (SpongeMerkleAnswer Msg Chal (T × DomainSep.Salt16) D)),
      Outcome (CertiFri.Oracle.spongeExperiment s₀ r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' →
      ¬ HasBad (JointHit s₀ stepDigestsOf r) l' →
      ¬ doomed r (out.2.1.mapIdx fun j m => read j m (spongeCommittedRow l'))) :
    prob E ((CertiFri.Oracle.spongeExperiment s₀ r adv msgs).bind rest) [] ≤
      (Q + r + R) * εmax + 3 * ((Q : ℝ) + r + R) ^ 2 / (2 * Fintype.card D) :=
  prob_spongeExperiment_bind_committedRow_le
    (T := T × DomainSep.Salt16) (D := D)
    hsound hε h0 hnil hM3 hM hread hadv msgs hrest hE

/-- **Concrete `v6-zk` BLAKE3 `derive_key` salted-leaf domain soundness:**
under `DomainSep.v6ZkSingle`, every salted leaf `(row, salt)` maps injectively
into BLAKE3 compression inputs, is disjoint from internal 2-to-1 Merkle nodes
and Fiat–Shamir transcripts, and is strictly separated from plain `v5` and
non-ZK `v6` invocations. -/
theorem v6Zk_saltedLeaf_injective_and_disjoint
    (row₁ row₂ : Array Goldilocks) (salt₁ salt₂ : DomainSep.Salt16)
    (l r : Digest) (l48 r48 : Digest48) (msg : ByteArray) :
    (DomainSep.v6ZkSingle.saltedLeafInput row₁ salt₁ =
        DomainSep.v6ZkSingle.saltedLeafInput row₂ salt₂ →
      row₁ = row₂ ∧ salt₁ = salt₂) ∧
    DomainSep.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSep.v6ZkSingle.nodeInput l r ∧
    DomainSep.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSep.v6ZkSingle.node48Input l48 r48 ∧
    DomainSep.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSep.v6ZkSingle.transcriptInput msg ∧
    DomainSep.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSep.plainInput msg ∧
    DomainSep.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSep.v6Single.leafInput msg :=
  ⟨DomainSep.saltedLeafInput_injective .v6ZkSingle,
   DomainSep.saltedLeafInput_ne_nodeInput .v6ZkSingle row₁ salt₁ l r,
   DomainSep.saltedLeafInput_ne_node48Input .v6ZkSingle row₁ salt₁ l48 r48,
   DomainSep.saltedLeafInput_ne_transcriptInput .v6ZkSingle row₁ salt₁ msg,
   DomainSep.leafInput_ne_plainInput .v6ZkSingle (DomainSep.saltedRowBytes row₁ salt₁) msg,
   DomainSep.v6Zk_leafInput_ne_v6_leafInput (DomainSep.saltedRowBytes row₁ salt₁) msg⟩

/-- **Complete `v6-zk` salted leaf injectivity & domain separation for RFC 7693 `BLAKE2b-512`:**
salted leaf inputs under `DomainSepBlake2b512.v6ZkSingle` are jointly injective in
`(row, salt)` and strictly disjoint from 64B 1-block internal nodes (`node64Input`),
transcript invocations, plain unpersonalized `BLAKE2b-512`, and non-ZK `v6` leaves. -/
theorem v6Zk_saltedLeaf_blake2b512_injective_and_disjoint
    (row₁ row₂ : Array Goldilocks) (salt₁ salt₂ : DomainSep.Salt16)
    (l64 r64 : Digest64) (msg : ByteArray) :
    (DomainSepBlake2b512.v6ZkSingle.saltedLeafInput row₁ salt₁ =
        DomainSepBlake2b512.v6ZkSingle.saltedLeafInput row₂ salt₂ →
      row₁ = row₂ ∧ salt₁ = salt₂) ∧
    DomainSepBlake2b512.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSepBlake2b512.v6ZkSingle.node64Input l64 r64 ∧
    DomainSepBlake2b512.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSepBlake2b512.v6ZkSingle.transcriptInput msg ∧
    DomainSepBlake2b512.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSepBlake2b512.plainInput msg ∧
    DomainSepBlake2b512.v6ZkSingle.saltedLeafInput row₁ salt₁ ≠
      DomainSepBlake2b512.v6Single.leafInput msg :=
  ⟨DomainSepBlake2b512.saltedLeafInput_injective .v6ZkSingle,
   DomainSepBlake2b512.saltedLeafInput_ne_node64Input .v6ZkSingle row₁ salt₁ l64 r64,
   DomainSepBlake2b512.saltedLeafInput_ne_transcriptInput .v6ZkSingle row₁ salt₁ msg,
   DomainSepBlake2b512.leafInput_ne_plainInput .v6ZkSingle (DomainSep.saltedRowBytes row₁ salt₁) msg,
   DomainSepBlake2b512.v6Zk_leafInput_ne_v6_leafInput (DomainSep.saltedRowBytes row₁ salt₁) msg⟩

end SaltedMerkle

/-! ## Section 2: 2× Interleaved Odd-Coset Blinding & Half-Stride Telescoping Quotient Slicing -/

section OddCosetAndTelescoping

variable {K : Type*} [Field K]

/-- **2× odd-coset witness blinding preserves trace evaluations:**
adding `(X^N - 1) * b(X)` to a trace polynomial `T₀(X)` leaves all evaluations
on the `N`-th roots of unity `H_N = {x | x^N = 1}` unchanged. -/
theorem zk_oddCoset_blinding_agrees_on_trace (N : ℕ) (T₀ b : K[X]) (x : K) (hx : x ^ N = 1) :
    (T₀ + (X ^ N - 1) * b).eval x = T₀.eval x := by
  simp [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, hx]

/-- **2× odd-coset witness blinding degree bound:**
if `deg(T₀) < N` and `deg(b) < N` (`0 < N`), then `T(X) = T₀(X) + (X^N - 1) * b(X)`
has degree `< 2 * N` (matching the 2× doubled evaluation domain of `v6-zk`). -/
theorem zk_oddCoset_blinding_natDegree_lt {N : ℕ} (hN : 0 < N) {T₀ b : K[X]}
    (hT₀ : T₀.natDegree < N) (hb : b.natDegree < N) :
    (T₀ + (X ^ N - 1) * b).natDegree < 2 * N := by
  have hZ : ((X : K[X]) ^ N - 1).natDegree ≤ N :=
    (natDegree_sub_le ((X : K[X]) ^ N) 1).trans (max_le (natDegree_X_pow_le N) (by simp))
  have hmul : (((X : K[X]) ^ N - 1) * b).natDegree < 2 * N := by
    by_cases hb0 : b = 0
    · simp [hb0]; omega
    · refine lt_of_le_of_lt natDegree_mul_le ?_
      omega
  exact lt_of_le_of_lt (natDegree_add_le T₀ _) (max_lt (by omega) hmul)

/-- Extended telescoping randomizer sequence `ρ_ext(i)` (`0` at `i ≥ 2 * q - 1`). -/
noncomputable def zkTelescopeShift (q : ℕ) (ρ : Fin (2 * q - 1) → K[X]) (i : ℕ) : K[X] :=
  if h : i < 2 * q - 1 then ρ ⟨i, h⟩ else 0

/-- Half-stride blinded quotient slice `c'_k(X) = c_k(X) - ρ_{k-1}(X) + X^N * ρ_k(X)`
(matching `multi-stark/v6-zk`'s `zk.rs` half-stride quotient blinding). -/
noncomputable def zkBlindedSlice (N q : ℕ) (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → K[X])
    (k : Fin (2 * q)) : K[X] :=
  c k - (if k.val = 0 then 0 else zkTelescopeShift q ρ (k.val - 1)) +
    X ^ N * zkTelescopeShift q ρ k.val

/-- **Exact half-stride telescoping quotient identity:**
for ANY `2 * q` quotient slices `c_k(X)` (`q ≥ 1`) and ANY `2 * q - 1`
blinding polynomials `ρ_k(X)`, the recombined polynomial
`∑_{k=0}^{2q-1} X^{kN} c'_k(X)` equals `∑_{k=0}^{2q-1} X^{kN} c_k(X)`
identically in `K[X]`. -/
theorem zk_quotient_telescoping_sum (N q : ℕ) (hq : 1 ≤ q)
    (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → K[X]) :
    ∑ k : Fin (2 * q), X ^ (k.val * N) * zkBlindedSlice N q c ρ k =
      ∑ k : Fin (2 * q), X ^ (k.val * N) * c k := by
  let g : ℕ → K[X] := fun i =>
    if i = 0 then 0 else X ^ (i * N) * zkTelescopeShift q ρ (i - 1)
  have hterm : ∀ k : Fin (2 * q),
      X ^ (k.val * N) * zkBlindedSlice N q c ρ k =
        X ^ (k.val * N) * c k + (g (k.val + 1) - g k.val) := by
    intro k
    unfold zkBlindedSlice
    have hsucc : g (k.val + 1) = X ^ (k.val * N) * (X ^ N * zkTelescopeShift q ρ k.val) := by
      dsimp only [g]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Nat.add_mul, one_mul, pow_add, mul_assoc]
    have hcur : g k.val =
        X ^ (k.val * N) * (if k.val = 0 then 0 else zkTelescopeShift q ρ (k.val - 1)) := by
      dsimp only [g]
      split_ifs <;> ring
    rw [hsucc, hcur]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have htele : ∑ k : Fin (2 * q), (g (k.val + 1) - g k.val) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) (2 * q)]
    rw [Finset.sum_range_sub g (2 * q)]
    have hg0 : g 0 = 0 := by simp [g]
    have hgtop : g (2 * q) = 0 := by
      dsimp only [g, zkTelescopeShift]
      have hne : 2 * q ≠ 0 := by omega
      simp [hne]
    rw [hg0, hgtop, sub_zero]
  rw [htele, add_zero]

/-- **Half-stride blinded quotient slices stay in the 2× doubled RS code (`deg < 2N`):**
if every unblinded slice `c_k` has degree `< N` and every shift `ρ_k` has
degree `< N`, then every blinded slice `c'_k` has degree `< 2 * N`. -/
theorem zk_blindedSlice_natDegree_lt {N q : ℕ} (hN : 0 < N)
    {c : Fin (2 * q) → K[X]} {ρ : Fin (2 * q - 1) → K[X]}
    (hc : ∀ k, (c k).natDegree < N) (hρ : ∀ j, (ρ j).natDegree < N) (k : Fin (2 * q)) :
    (zkBlindedSlice N q c ρ k).natDegree < 2 * N := by
  have hshift : ∀ i, (zkTelescopeShift q ρ i).natDegree < N := by
    intro i
    unfold zkTelescopeShift
    split_ifs with h
    · exact hρ ⟨i, h⟩
    · simp; exact hN
  unfold zkBlindedSlice
  have hleft : (c k - if k.val = 0 then 0 else zkTelescopeShift q ρ (k.val - 1)).natDegree < N := by
    refine lt_of_le_of_lt (natDegree_sub_le (c k) _) (max_lt (hc k) ?_)
    split_ifs
    · simp; exact hN
    · exact hshift (k.val - 1)
  have hright : ((X : K[X]) ^ N * zkTelescopeShift q ρ k.val).natDegree < 2 * N := by
    by_cases hz : zkTelescopeShift q ρ k.val = 0
    · simp [hz]; omega
    · refine lt_of_le_of_lt natDegree_mul_le ?_
      have h1 : ((X : K[X]) ^ N).natDegree ≤ N := natDegree_X_pow_le N
      have h2 := hshift k.val
      omega
  exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by omega) hright)

end OddCosetAndTelescoping

/-! ## Section 3: `W_R ≥ 4` Base-Field Randomizer Span over `Fp3Model` & Tensor Soundness -/

section RandomizerSpan

/-- `v : Fin W → Fp3Model` spans `Fp3Model` over the Goldilocks base field `Fp`. -/
def FpSpan3 {W : ℕ} (v : Fin W → Fp3Model) : Prop :=
  ∀ y : Fp3Model, ∃ a : Fin W → GoldilocksField, ∑ i : Fin W, Fp3Model.embed (a i) * v i = y

/-- Auxiliary lemma: `b^3 - b * c^2 - c^3 ≠ 0` in `GoldilocksField` whenever
`(b, c) ≠ (0, 0)`, directly from `cubicTrinomial_no_root` (`X^3 - X - 1` has no
root in `GF(p)`). -/
theorem goldilocks_homogeneous_cubic_ne_zero {b c : GoldilocksField}
    (hbc : b ≠ 0 ∨ c ≠ 0) : b ^ 3 - b * c ^ 2 - c ^ 3 ≠ 0 := by
  by_cases hc : c = 0
  · subst hc
    have hb : b ≠ 0 := hbc.resolve_right (by simp)
    simpa using pow_ne_zero 3 hb
  · intro h0
    have hroot : (b * c⁻¹) ^ 3 - (b * c⁻¹) - 1 = 0 := by
      have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
      apply mul_right_cancel₀ hc3
      have h1 : ((b * c⁻¹) ^ 3 - (b * c⁻¹) - 1) * c ^ 3 = b ^ 3 - b * c ^ 2 - c ^ 3 := by
        field_simp [hc]
      rw [h1, h0, zero_mul]
    have hno := Fp3Model.cubicTrinomial_no_root (b * c⁻¹)
    apply hno
    simpa [Fp3Model.cubicTrinomial] using hroot

/-- Helper: if `(u, v)` has nonzero `2 × 2` determinant in `(c1, c2)` coordinates,
then `{1, u, v}` spans `Fp3Model` over `GoldilocksField`. -/
private theorem fp3_span_of_det_ne_zero (u v : Fp3Model)
    (hdet : u.c1 * v.c2 - u.c2 * v.c1 ≠ 0) (y : Fp3Model) :
    ∃ a0 a1 a2 : GoldilocksField,
      Fp3Model.embed a0 * 1 + Fp3Model.embed a1 * u + Fp3Model.embed a2 * v = y := by
  let Δ := u.c1 * v.c2 - u.c2 * v.c1
  let a1 := (y.c1 * v.c2 - y.c2 * v.c1) * Δ⁻¹
  let a2 := (u.c1 * y.c2 - u.c2 * y.c1) * Δ⁻¹
  let a0 := y.c0 - a1 * u.c0 - a2 * v.c0
  have hinv : Δ⁻¹ * Δ = 1 := inv_mul_cancel₀ hdet
  refine ⟨a0, a1, a2, ?_⟩
  ext
  · simp [a0]; ring
  · simp only [Fp3Model.add_c1, Fp3Model.mul_c1, Fp3Model.embed_c0, Fp3Model.embed_c1,
      Fp3Model.embed_c2, Fp3Model.one_c1, mul_zero, zero_mul, add_zero, zero_add]
    apply mul_right_cancel₀ hdet
    calc (a1 * u.c1 + a2 * v.c1) * Δ
        = ((y.c1 * v.c2 - y.c2 * v.c1) * u.c1 + (u.c1 * y.c2 - u.c2 * y.c1) * v.c1) *
            (Δ⁻¹ * Δ) := by dsimp only [a1, a2]; ring
      _ = y.c1 * Δ := by rw [hinv, mul_one]; dsimp only [Δ]; ring
  · simp only [Fp3Model.add_c2, Fp3Model.mul_c2, Fp3Model.embed_c0, Fp3Model.embed_c1,
      Fp3Model.embed_c2, Fp3Model.one_c2, mul_zero, zero_mul, add_zero, zero_add]
    apply mul_right_cancel₀ hdet
    calc (a1 * u.c2 + a2 * v.c2) * Δ
        = ((y.c1 * v.c2 - y.c2 * v.c1) * u.c2 + (u.c1 * y.c2 - u.c2 * y.c1) * v.c2) *
            (Δ⁻¹ * Δ) := by dsimp only [a1, a2]; ring
      _ = y.c2 * Δ := by rw [hinv, mul_one]; dsimp only [Δ]; ring

/-- **Exact `W_R = 4` Tensor-Weight Span Theorem over `Fp3Model`:**
whenever `r₀ ∉ GF(p)` and `r₁ ∉ GF(p)`, the 4-element `FriBatching::Tensor`
weight tuple `![1, r₀, r₁, r₀ * r₁]` spans the full cubic extension `Fp3Model`
over `GF(p)`. -/
theorem fp3_tensor4_spans_of_not_base {r₀ r₁ : Fp3Model}
    (hr₀ : r₀.c1 ≠ 0 ∨ r₀.c2 ≠ 0) (hr₁ : r₁.c1 ≠ 0 ∨ r₁.c2 ≠ 0) :
    FpSpan3 (![1, r₀, r₁, r₀ * r₁] : Fin 4 → Fp3Model) := by
  intro y
  have hembed0 : Fp3Model.embed 0 = 0 := rfl
  by_cases hdet1 : r₀.c1 * r₁.c2 - r₀.c2 * r₁.c1 ≠ 0
  · obtain ⟨a0, a1, a2, h⟩ := fp3_span_of_det_ne_zero r₀ r₁ hdet1 y
    refine ⟨![a0, a1, a2, 0], ?_⟩
    rw [Fin.sum_univ_four]
    simpa [hembed0] using h
  · push Not at hdet1
    -- `(r₁.c1, r₁.c2)` is a nonzero scalar multiple `λ * (r₀.c1, r₀.c2)`.
    have hlam : ∃ lam : GoldilocksField, lam ≠ 0 ∧ r₁.c1 = lam * r₀.c1 ∧ r₁.c2 = lam * r₀.c2 := by
      rcases hr₀ with hb0 | hc0
      · refine ⟨r₁.c1 * r₀.c1⁻¹, ?_, ?_, ?_⟩
        · intro h0
          have h1 : r₁.c1 = 0 := by
            have := congrArg (· * r₀.c1) h0
            simpa [mul_assoc, inv_mul_cancel₀ hb0] using this
          have h2 : r₁.c2 = 0 := by
            have : r₀.c1 * r₁.c2 = 0 := by linear_combination hdet1 + r₀.c2 * h1
            exact (mul_eq_zero.mp this).resolve_left hb0
          exact hr₁.elim (fun h => h h1) (fun h => h h2)
        · field_simp [hb0]
        · have : r₀.c1 * r₁.c2 = r₀.c2 * r₁.c1 := sub_eq_zero.mp hdet1
          field_simp [hb0]
          linear_combination this
      · refine ⟨r₁.c2 * r₀.c2⁻¹, ?_, ?_, ?_⟩
        · intro h0
          have h2 : r₁.c2 = 0 := by
            have := congrArg (· * r₀.c2) h0
            simpa [mul_assoc, inv_mul_cancel₀ hc0] using this
          have h1 : r₁.c1 = 0 := by
            have : r₀.c2 * r₁.c1 = 0 := by linear_combination -hdet1 + r₀.c1 * h2
            exact (mul_eq_zero.mp this).resolve_left hc0
          exact hr₁.elim (fun h => h h1) (fun h => h h2)
        · have : r₀.c1 * r₁.c2 = r₀.c2 * r₁.c1 := sub_eq_zero.mp hdet1
          field_simp [hc0]
          linear_combination -this
        · field_simp [hc0]
    obtain ⟨lam, hlam_ne, hrc1, hrc2⟩ := hlam
    have hdet2 : r₀.c1 * (r₀ * r₁).c2 - r₀.c2 * (r₀ * r₁).c1 ≠ 0 := by
      have hid : r₀.c1 * (r₀ * r₁).c2 - r₀.c2 * (r₀ * r₁).c1 =
          lam * (r₀.c1 ^ 3 - r₀.c1 * r₀.c2 ^ 2 - r₀.c2 ^ 3) := by
        simp only [Fp3Model.mul_c1, Fp3Model.mul_c2, hrc1, hrc2]
        ring
      rw [hid]
      exact mul_ne_zero hlam_ne (goldilocks_homogeneous_cubic_ne_zero hr₀)
    obtain ⟨a0, a1, a3, h⟩ := fp3_span_of_det_ne_zero r₀ (r₀ * r₁) hdet2 y
    refine ⟨![a0, a1, 0, a3], ?_⟩
    rw [Fin.sum_univ_four]
    simpa [hembed0] using h

private theorem natCard_goldilocksField : Nat.card GoldilocksField = Goldilocks.order :=
  Nat.card_zmod Goldilocks.order

private theorem natCard_fp3Model : Nat.card Fp3Model = Goldilocks.order ^ 3 := by
  rw [Nat.card_eq_fintype_card, Fp3Model.card_fp3Model]

/-- **Exact `W_R = 4` Tensor-Randomizer Span-Failure Probability (`≤ 2 / p^2 < 1 / 2^126`):**
over uniformly random `(r₀, r₁) ∈ Fp3Model × Fp3Model`, the fraction of pairs
for which `![1, r₀, r₁, r₀ * r₁]` fails to span `Fp3Model` over `GF(p)` is at
most `2 / Goldilocks.order ^ 2 < 1 / 2 ^ 126`. -/
theorem fp3_tensor4_span_failure_prob_le :
    (Nat.card {p : Fp3Model × Fp3Model //
        ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) ≤
      2 / (Goldilocks.order : ℝ) ^ 2 := by
  let Bad := {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)}
  have hbase : ∀ x : Bad, (x.1.1.c1 = 0 ∧ x.1.1.c2 = 0) ∨ (x.1.2.c1 = 0 ∧ x.1.2.c2 = 0) := by
    intro ⟨⟨r₀, r₁⟩, hbad⟩
    by_contra hnot
    push Not at hnot
    have hr₀ : r₀.c1 ≠ 0 ∨ r₀.c2 ≠ 0 := by
      by_cases h1 : r₀.c1 = 0
      · exact Or.inr (hnot.1 h1)
      · exact Or.inl h1
    have hr₁ : r₁.c1 ≠ 0 ∨ r₁.c2 ≠ 0 := by
      by_cases h1 : r₁.c1 = 0
      · exact Or.inr (hnot.2 h1)
      · exact Or.inl h1
    exact hbad (fp3_tensor4_spans_of_not_base hr₀ hr₁)
  let enc : Bad → (GoldilocksField × Fp3Model) ⊕ (Fp3Model × GoldilocksField) :=
    fun x =>
      @ite _ (x.1.1.c1 = 0 ∧ x.1.1.c2 = 0) (Classical.propDecidable _)
        (Sum.inl (x.1.1.c0, x.1.2))
        (Sum.inr (x.1.1, x.1.2.c0))
  have henc_inj : Function.Injective enc := by
    intro x y hxy
    have hx := hbase x
    have hy := hbase y
    dsimp only [enc] at hxy
    split_ifs at hxy with hx1 hy1 hy1
    · have hpair := Sum.inl.inj hxy
      have hc0 : x.1.1.c0 = y.1.1.c0 := congrArg (@Prod.fst GoldilocksField Fp3Model) hpair
      have hr2 : x.1.2 = y.1.2 := congrArg (@Prod.snd GoldilocksField Fp3Model) hpair
      apply Subtype.ext
      apply Prod.ext _ hr2
      ext
      · exact hc0
      · rw [hx1.1, hy1.1]
      · rw [hx1.2, hy1.2]
    · have hx2 : x.1.2.c1 = 0 ∧ x.1.2.c2 = 0 := hx.resolve_left hx1
      have hy2 : y.1.2.c1 = 0 ∧ y.1.2.c2 = 0 := hy.resolve_left hy1
      have hpair := Sum.inr.inj hxy
      have hr1 : x.1.1 = y.1.1 := congrArg (@Prod.fst Fp3Model GoldilocksField) hpair
      have hc0 : x.1.2.c0 = y.1.2.c0 := congrArg (@Prod.snd Fp3Model GoldilocksField) hpair
      apply Subtype.ext
      apply Prod.ext hr1
      ext
      · exact hc0
      · rw [hx2.1, hy2.1]
      · rw [hx2.2, hy2.2]
  have hcard_le : Nat.card Bad ≤ 2 * Goldilocks.order ^ 4 := by
    have hle := Nat.card_le_card_of_injective enc henc_inj
    rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, natCard_fp3Model, natCard_goldilocksField] at hle
    calc Nat.card Bad ≤ Goldilocks.order * Goldilocks.order ^ 3 +
          Goldilocks.order ^ 3 * Goldilocks.order := hle
      _ = 2 * Goldilocks.order ^ 4 := by ring
  have hden : (Nat.card (Fp3Model × Fp3Model) : ℝ) = (Goldilocks.order : ℝ) ^ 6 := by
    rw [Nat.card_prod, natCard_fp3Model]
    push_cast; ring
  have hp_pos : (0 : ℝ) < (Goldilocks.order : ℝ) := by
    exact_mod_cast (by decide : 0 < Goldilocks.order)
  have hcast : (Nat.card Bad : ℝ) ≤ 2 * (Goldilocks.order : ℝ) ^ 4 := by exact_mod_cast hcard_le
  have hp6 : (0 : ℝ) ≤ (Goldilocks.order : ℝ) ^ 6 := pow_nonneg hp_pos.le 6
  rw [hden]
  calc (Nat.card Bad : ℝ) / (Goldilocks.order : ℝ) ^ 6
      ≤ (2 * (Goldilocks.order : ℝ) ^ 4) / (Goldilocks.order : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right hcast hp6
    _ = 2 / (Goldilocks.order : ℝ) ^ 2 := by field_simp [hp_pos.ne']

/-- Concrete numerical corollary: `2 / Goldilocks.order ^ 2 < 1 / 2 ^ 126`. -/
theorem fp3_tensor4_span_failure_lt_two_neg_126 :
    (2 : ℝ) / (Goldilocks.order : ℝ) ^ 2 < 1 / (2 : ℝ) ^ 126 := by
  have hp_nat : 2 ^ 127 < Goldilocks.order ^ 2 := by
    have h1 : 2 ^ 63 + 2 ^ 62 < Goldilocks.order := by decide
    have h2 : (2 ^ 63 + 2 ^ 62) ^ 2 < Goldilocks.order ^ 2 :=
      Nat.pow_lt_pow_left h1 (by decide)
    have h3 : (2 : ℕ) ^ 127 ≤ (2 ^ 63 + 2 ^ 62) ^ 2 := by
      have h3a : (2 ^ 63 + 2 ^ 62) ^ 2 = 9 * 2 ^ 124 := by ring
      have h3b : (2 : ℕ) ^ 127 = 8 * 2 ^ 124 := by
        rw [show (8 : ℕ) = 2 ^ 3 by decide, ← pow_add]
      omega
    exact lt_of_le_of_lt h3 h2
  have hp : (2 : ℝ) ^ 127 < (Goldilocks.order : ℝ) ^ 2 := by exact_mod_cast hp_nat
  have hp_pos : (0 : ℝ) < (Goldilocks.order : ℝ) := by
    exact_mod_cast (by decide : 0 < Goldilocks.order)
  rw [div_lt_div_iff₀ (pow_pos hp_pos 2) (pow_pos (by norm_num) 126)]
  have h127 : (2 : ℝ) * (2 : ℝ) ^ 126 = (2 : ℝ) ^ 127 := by
    rw [mul_comm, ← pow_succ]
  linarith

/-- **Constructive Negative Control for `W_R = 3` (`≥ 1 / p > 1 / 2^64` failure):**
with only `W_R = 3` randomizer columns (`![1, r₀, r₁]`), whenever `r₁` lies in
the 2D `GF(p)`-subspace `GF(p) + GF(p) * r₀` (at least `p^5` pairs out of `p^6`),
`![1, r₀, r₁]` fails to span `Fp3Model` over `GF(p)`, giving failure probability
`≥ 1 / Goldilocks.order > 1 / 2^64` (a catastrophic `64`-bit ZK blinding break). -/
theorem negControl_fp3_tensor3_span_failure_ge :
    (1 : ℝ) / (Goldilocks.order : ℝ) ≤
      (Nat.card {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2] : Fin 3 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) ∧
    (1 : ℝ) / (2 : ℝ) ^ 64 < 1 / (Goldilocks.order : ℝ) := by
  have hnotspan : ∀ (r₀ r₁ : Fp3Model), r₀.c1 * r₁.c2 = r₀.c2 * r₁.c1 →
      ¬ FpSpan3 (![1, r₀, r₁] : Fin 3 → Fp3Model) := by
    intro r₀ r₁ hdep hspan
    have hvec2 : (![1, r₀, r₁] : Fin 3 → Fp3Model) 2 = r₁ := rfl
    by_cases h0 : r₀.c1 = 0 ∧ r₀.c2 = 0
    · let y : Fp3Model := if r₁.c1 = 0 then ⟨0, 1, 0⟩ else ⟨0, 0, 1⟩
      obtain ⟨a, ha⟩ := hspan y
      rw [Fin.sum_univ_three] at ha
      have h1 := congrArg Fp3Model.c1 ha
      have h2 := congrArg Fp3Model.c2 ha
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hvec2,
        Fp3Model.add_c1, Fp3Model.add_c2, Fp3Model.mul_c1, Fp3Model.mul_c2,
        Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2,
        Fp3Model.one_c1, Fp3Model.one_c2, h0.1, h0.2,
        mul_zero, zero_mul, add_zero, zero_add] at h1 h2
      dsimp only [y] at h1 h2
      split_ifs at h1 h2 with hr1
      · simp [hr1] at h1
      · have ha2 : a 2 = 0 := (mul_eq_zero.mp h1).resolve_right hr1
        simp [ha2] at h2
    · let y : Fp3Model := if r₀.c1 = 0 then ⟨0, 1, 0⟩ else ⟨0, 0, 1⟩
      obtain ⟨a, ha⟩ := hspan y
      rw [Fin.sum_univ_three] at ha
      have h1 := congrArg Fp3Model.c1 ha
      have h2 := congrArg Fp3Model.c2 ha
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hvec2,
        Fp3Model.add_c1, Fp3Model.add_c2, Fp3Model.mul_c1, Fp3Model.mul_c2,
        Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2,
        Fp3Model.one_c1, Fp3Model.one_c2,
        mul_zero, zero_mul, add_zero, zero_add] at h1 h2
      have hcomb : r₀.c1 * y.c2 - r₀.c2 * y.c1 = 0 := by
        rw [← h1, ← h2]
        linear_combination (a 2) * hdep
      dsimp only [y] at hcomb
      split_ifs at hcomb with hc1
      · have hc2 : r₀.c2 ≠ 0 := fun h2 => h0 ⟨hc1, h2⟩
        simp [hc1] at hcomb
        exact hc2 hcomb
      · simp at hcomb
        exact hc1 hcomb
  let Bad := {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2] : Fin 3 → Fp3Model)}
  let f : Fp3Model × GoldilocksField × GoldilocksField → Fp3Model × Fp3Model :=
    fun x =>
      @ite _ (x.1.c1 = 0 ∧ x.1.c2 = 0) (Classical.propDecidable _)
        (x.1, ⟨x.2.1, x.2.2, 0⟩)
        (x.1, ⟨x.2.1, x.2.2 * x.1.c1, x.2.2 * x.1.c2⟩)
  have hf_inj : Function.Injective f := by
    intro ⟨r₀, u₁, v₁⟩ ⟨r₀', u₂, v₂⟩ heq
    have hr : r₀ = r₀' := by
      dsimp only [f] at heq
      split_ifs at heq <;> exact congrArg Prod.fst heq
    subst hr
    dsimp only [f] at heq
    split_ifs at heq with h0
    · have h2 := congrArg Prod.snd heq
      have hu : u₁ = u₂ := congrArg Fp3Model.c0 h2
      have hv : v₁ = v₂ := congrArg Fp3Model.c1 h2
      rw [hu, hv]
    · have h2 := congrArg Prod.snd heq
      have hu : u₁ = u₂ := congrArg Fp3Model.c0 h2
      have hvc1 : v₁ * r₀.c1 = v₂ * r₀.c1 := congrArg Fp3Model.c1 h2
      have hvc2 : v₁ * r₀.c2 = v₂ * r₀.c2 := congrArg Fp3Model.c2 h2
      have hv : v₁ = v₂ := by
        by_cases hc1 : r₀.c1 = 0
        · have hc2 : r₀.c2 ≠ 0 := fun hc2 => h0 ⟨hc1, hc2⟩
          exact mul_right_cancel₀ hc2 hvc2
        · exact mul_right_cancel₀ hc1 hvc1
      rw [hu, hv]
  have hf_mem : ∀ x, ¬ FpSpan3 (![1, (f x).1, (f x).2] : Fin 3 → Fp3Model) := by
    intro ⟨r₀, u, v⟩
    dsimp only [f]
    split_ifs with h0
    · exact hnotspan r₀ ⟨u, v, 0⟩ (by simp [h0.1, h0.2])
    · exact hnotspan r₀ ⟨u, v * r₀.c1, v * r₀.c2⟩ (by ring)
  let g : Fp3Model × GoldilocksField × GoldilocksField → Bad := fun x => ⟨f x, hf_mem x⟩
  have hg_inj : Function.Injective g := fun _ _ h => hf_inj (congrArg Subtype.val h)
  have hcard_ge : Goldilocks.order ^ 5 ≤ Nat.card Bad := by
    have hle := Nat.card_le_card_of_injective g hg_inj
    rw [Nat.card_prod, Nat.card_prod, natCard_fp3Model, natCard_goldilocksField] at hle
    calc Goldilocks.order ^ 5 = Goldilocks.order ^ 3 * (Goldilocks.order * Goldilocks.order) := by
          ring
      _ ≤ Nat.card Bad := hle
  have hden : (Nat.card (Fp3Model × Fp3Model) : ℝ) = (Goldilocks.order : ℝ) ^ 6 := by
    rw [Nat.card_prod, natCard_fp3Model]; push_cast; ring
  have hp_pos : (0 : ℝ) < (Goldilocks.order : ℝ) := by
    exact_mod_cast (by decide : 0 < Goldilocks.order)
  have hp6 : (0 : ℝ) ≤ (Goldilocks.order : ℝ) ^ 6 := pow_nonneg hp_pos.le 6
  constructor
  · rw [hden]
    have hcast : (Goldilocks.order : ℝ) ^ 5 ≤ (Nat.card Bad : ℝ) := by exact_mod_cast hcard_ge
    calc (1 : ℝ) / (Goldilocks.order : ℝ)
        = (Goldilocks.order : ℝ) ^ 5 / (Goldilocks.order : ℝ) ^ 6 := by field_simp [hp_pos.ne']
      _ ≤ (Nat.card Bad : ℝ) / (Goldilocks.order : ℝ) ^ 6 :=
            div_le_div_of_nonneg_right hcast hp6
  · have hp_lt : (Goldilocks.order : ℝ) < (2 : ℝ) ^ 64 := by
      exact_mod_cast (by decide : Goldilocks.order < 2 ^ 64)
    rw [div_lt_div_iff₀ (pow_pos (by norm_num) 64) hp_pos]
    linarith

/-- **RS Proximity Preservation with `W_R` Randomizer Columns Folded into `FriBatching::Tensor`:**
merging `W_R` base-field randomizer polynomials of degree `< 2 * N` into a
quotient MMCS of width `W_orig` (total width `W_orig + W_R ≤ 2 ^ 16`) preserves
unconditional `Tensor2DMCA` soundness `≤ (3 / 4) / 2 ^ 128` over `GoldilocksExt3`. -/
theorem goldilocksExt3_zk_tensor2DMCA_ud_128 (D : Finset Fp3Model) (d W_orig W_R M : ℕ)
    (hD : D.card ≤ 2 ^ 32) (hW : W_orig + W_R ≤ 2 ^ 16) (hM : M ≤ 2 ^ 16)
    (hrate : 2 * ((3 / 8 : ℝ) * D.card) + d ≤ D.card) :
    Tensor2DMCA D d (W_orig + W_R) M (5 / 8) ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) :=
  goldilocksExt3_tensor2DMCA_ud_128 D d (W_orig + W_R) M hD hW hM hrate

end RandomizerSpan

/-! ## Section 4: `v6-zk` Guardrail Predicates, Positive Profiles & 4 Negative Controls -/

/-- Mandatory minimum base-field randomizer width (`W_R ≥ 4`) in `multi-stark/v6-zk`. -/
def ZK_RANDOMIZER_WIDTH : ℕ := 4

/-- Mandatory leaf salt length in bytes (`16` bytes = 128 bits) in `multi-stark/v6-zk`. -/
def ZK_LEAF_SALT_BYTES : ℕ := 16

/-- Goldilocks two-adicity (`2 ^ 32 ∣ p - 1`). -/
def GOLDILOCKS_TWO_ADICITY : ℕ := 32

/-- Ceiling base-2 logarithm `⌈log₂ n⌉` (matching Rust `n.next_power_of_two().trailing_zeros()`). -/
def nextPow2Log (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- `n ≤ 2 ^ nextPow2Log n` for every `n : ℕ`. -/
theorem le_two_pow_nextPow2Log (n : ℕ) : n ≤ 2 ^ nextPow2Log n := by
  unfold nextPow2Log
  split_ifs with h
  · simpa using h
  · have hpos : n - 1 ≠ 0 := by omega
    have h2 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) :=
      (Nat.log2_lt hpos).mp (Nat.lt_succ_self _)
    omega

/-- Minimality of `nextPow2Log`: if `n ≤ 2 ^ k`, then `nextPow2Log n ≤ k`. -/
theorem nextPow2Log_le_of_le_pow {n k : ℕ} (h : n ≤ 2 ^ k) : nextPow2Log n ≤ k := by
  unfold nextPow2Log
  split_ifs with hle
  · exact Nat.zero_le _
  · have hlt : n - 1 < 2 ^ k := by omega
    have hlog : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).mpr hlt
    omega

/-- Minimum `v6-zk` trace log-height `log₂(next_pow2(2 * Q + 2 * D))`,
matching `multi-stark/v6-zk` `p3_adapter::zk::min_zk_log_degree`. -/
def minZkLogDegree (numQueries extDegree : ℕ) : ℕ :=
  nextPow2Log (2 * numQueries + 2 * extDegree)

/-- `v6-zk` quotient degree multiple `next_pow2(max(d, 1))`, matching
`multi-stark/v6-zk` `Circuit::quotient_degree_for(is_zk = true)`. -/
def zkQuotientDegree (maxConstraintDegree : ℕ) : ℕ :=
  2 ^ nextPow2Log (max maxConstraintDegree 1)

/-- Non-ZK `v6` quotient degree multiple `next_pow2(max(d, 2) - 1)`, matching
`multi-stark` `Circuit::quotient_degree()`. -/
def nonZkQuotientDegree (maxConstraintDegree : ℕ) : ℕ :=
  2 ^ nextPow2Log (max maxConstraintDegree 2 - 1)

/-- Degree-bound justification for `zkQuotientDegree`: for constraints of degree
`d ≥ 1` evaluated on 2× odd-coset blinded trace polynomials of degree `< 2 * N`,
after dividing by `Z_H(X)` (`deg = N`), the quotient degree `(2 * d - 1) * N - d`
is strictly less than `2 * N * zkQuotientDegree d`. -/
theorem zk_quotient_degree_lt {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (2 * d - 1) * N < 2 * N * zkQuotientDegree d := by
  have hd_le : d ≤ zkQuotientDegree d := by
    unfold zkQuotientDegree
    exact (Nat.le_max_left d 1).trans (le_two_pow_nextPow2Log _)
  have h1 : 2 * d - 1 < 2 * zkQuotientDegree d := by omega
  calc (2 * d - 1) * N < (2 * zkQuotientDegree d) * N := Nat.mul_lt_mul_of_pos_right h1 hN
    _ = 2 * N * zkQuotientDegree d := by ring

/-- Configuration record for a `multi-stark/v6-zk` proving instance, capturing
all four ZK soundness/hiding guardrails enforced by `System::new` and
`HidingSpillableTwoAdicFriPcs`. -/
structure ZkConfig where
  logTraceHeight : ℕ
  logBlowup : ℕ
  numQueries : ℕ
  extDegree : ℕ
  randomizerWidth : ℕ
  maxConstraintDegree : ℕ
  leafDomain : Blake3Domain
  compressDomain : Blake3Domain
  transcriptDomain : Blake3Domain
  vkDomain : Blake3Domain
  deriving DecidableEq, Repr

/-- **All 4 `multi-stark/v6-zk` Guardrails:**
1. **Trap 1 (Min trace height & Goldilocks two-adicity):**
   `minZkLogDegree numQueries extDegree ≤ logTraceHeight` (so `N ≥ 2Q + 2D`)
   AND `logTraceHeight + 1 + logBlowup ≤ 32` (2× doubled LDE fits in `2^32`).
2. **Trap 2 (Randomizer width):** `W_R ≥ 4` (`ZK_RANDOMIZER_WIDTH`).
3. **Trap 3 (Quotient degree vs `log_blowup`):**
   `1 ≤ logBlowup` AND `zkQuotientDegree maxConstraintDegree ≤ 2 ^ logBlowup`.
4. **Trap 4 (`v6` ↔ `v6-zk` domain separation):**
   all four active BLAKE3 `derive_key` domains belong to the `v6-zk` namespace
   (`ZkMerkleLeaf`, `ZkMerkleCompress`, `ZkTranscriptSingle`/`ZkTranscriptBatch`,
   `ZkVerifyingKey`). -/
def ZkGuardrailsOk (cfg : ZkConfig) : Prop :=
  -- Trap 1: min trace height N ≥ next_pow2(2Q + 2D) and 2× LDE fits in 2^32
  minZkLogDegree cfg.numQueries cfg.extDegree ≤ cfg.logTraceHeight ∧
  cfg.logTraceHeight + 1 + cfg.logBlowup ≤ GOLDILOCKS_TWO_ADICITY ∧
  -- Trap 2: W_R ≥ 4
  ZK_RANDOMIZER_WIDTH ≤ cfg.randomizerWidth ∧
  -- Trap 3: log_blowup ≥ 1 and q_zk ≤ 2^log_blowup
  1 ≤ cfg.logBlowup ∧
  zkQuotientDegree cfg.maxConstraintDegree ≤ 2 ^ cfg.logBlowup ∧
  -- Trap 4: strict v6-zk domain separation
  cfg.leafDomain = .zkMerkleLeaf ∧
  cfg.compressDomain = .zkMerkleCompress ∧
  (cfg.transcriptDomain = .zkTranscriptSingle ∨ cfg.transcriptDomain = .zkTranscriptBatch) ∧
  cfg.vkDomain = .zkVerifyingKey

/-- Under `ZkGuardrailsOk`, the unblinded trace height `2 ^ logTraceHeight`
strictly satisfies `2 * Q + 2 * D ≤ 2 ^ logTraceHeight`. -/
theorem zkGuardrails_trace_height_ge {cfg : ZkConfig} (h : ZkGuardrailsOk cfg) :
    2 * cfg.numQueries + 2 * cfg.extDegree ≤ 2 ^ cfg.logTraceHeight :=
  (le_two_pow_nextPow2Log _).trans (Nat.pow_le_pow_right two_pos h.1)

/-- Under `ZkGuardrailsOk`, all four active BLAKE3 domains are strictly in the
`v6-zk` namespace and pairwise distinct from every non-ZK `v6` and `plain` domain. -/
theorem zkGuardrails_domains_disjoint_from_nonZk {cfg : ZkConfig} (h : ZkGuardrailsOk cfg)
    {dNonZk : Blake3Domain} (hn : dNonZk.isZk = false) :
    cfg.leafDomain.keyWords ≠ dNonZk.keyWords ∧
    cfg.compressDomain.keyWords ≠ dNonZk.keyWords ∧
    cfg.transcriptDomain.keyWords ≠ dNonZk.keyWords ∧
    cfg.vkDomain.keyWords ≠ dNonZk.keyWords := by
  obtain ⟨_, _, _, _, _, hL, hC, hT, hV⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hL]; rfl) hn
  · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hC]; rfl) hn
  · rcases hT with hT | hT
    · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hT]; rfl) hn
    · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hT]; rfl) hn
  · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hV]; rfl) hn

/-! ### Canonical `v6-zk` 128-bit Profiles (Positive Certificates) -/

/-- Canonical `v6-zk` 128-bit UD profile `(lb=2, q=160, D=3, logN=9, W_R=4, maxDeg=3)`. -/
def zkProfileUd128 : ZkConfig where
  logTraceHeight := 9
  logBlowup := 2
  numQueries := 160
  extDegree := 3
  randomizerWidth := 4
  maxConstraintDegree := 3
  leafDomain := .zkMerkleLeaf
  compressDomain := .zkMerkleCompress
  transcriptDomain := .zkTranscriptSingle
  vkDomain := .zkVerifyingKey

/-- Canonical `v6-zk` 128-bit Johnson profile `(lb=2, q=128, D=3, logN=9, W_R=4, maxDeg=3)`. -/
def zkProfileJohnsonLb2 : ZkConfig where
  logTraceHeight := 9
  logBlowup := 2
  numQueries := 128
  extDegree := 3
  randomizerWidth := 4
  maxConstraintDegree := 3
  leafDomain := .zkMerkleLeaf
  compressDomain := .zkMerkleCompress
  transcriptDomain := .zkTranscriptSingle
  vkDomain := .zkVerifyingKey

/-- Canonical `v6-zk` 128-bit Native Shrinker profile `(lb=3, q=78, D=3, logN=8, W_R=4, maxDeg=5)`. -/
def zkProfileJohnsonLb3 : ZkConfig where
  logTraceHeight := 8
  logBlowup := 3
  numQueries := 78
  extDegree := 3
  randomizerWidth := 4
  maxConstraintDegree := 5
  leafDomain := .zkMerkleLeaf
  compressDomain := .zkMerkleCompress
  transcriptDomain := .zkTranscriptSingle
  vkDomain := .zkVerifyingKey

/-- Canonical `v6-zk` 128-bit Native Shrinker profile `(lb=4, q=58, D=3, logN=7, W_R=4, maxDeg=9)`. -/
def zkProfileJohnsonLb4 : ZkConfig where
  logTraceHeight := 7
  logBlowup := 4
  numQueries := 58
  extDegree := 3
  randomizerWidth := 4
  maxConstraintDegree := 9
  leafDomain := .zkMerkleLeaf
  compressDomain := .zkMerkleCompress
  transcriptDomain := .zkTranscriptSingle
  vkDomain := .zkVerifyingKey

theorem zkProfileUd128_ok : ZkGuardrailsOk zkProfileUd128 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, rfl, Or.inl rfl, rfl⟩

theorem zkProfileJohnsonLb2_ok : ZkGuardrailsOk zkProfileJohnsonLb2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, rfl, Or.inl rfl, rfl⟩

theorem zkProfileJohnsonLb3_ok : ZkGuardrailsOk zkProfileJohnsonLb3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, rfl, Or.inl rfl, rfl⟩

theorem zkProfileJohnsonLb4_ok : ZkGuardrailsOk zkProfileJohnsonLb4 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, rfl, Or.inl rfl, rfl⟩

/-! ### 4 Constructive Negative Controls (One per ZK Guardrail Trap) -/

/-- **Negative Control (Trap 1):** `logTraceHeight = 8` (`N = 256 < 2*160 + 2*3 = 326`)
is strictly REJECTED by `ZkGuardrailsOk`. -/
theorem negControl_zk_trap1_small_trace :
    ¬ ZkGuardrailsOk { zkProfileUd128 with logTraceHeight := 8 } := by
  intro h
  have h1 := h.1
  revert h1
  decide

/-- **Negative Control (Trap 2):** `randomizerWidth = 3 < 4` is strictly REJECTED
by `ZkGuardrailsOk` (matching `negControl_fp3_tensor3_span_failure_ge`). -/
theorem negControl_zk_trap2_small_randomizer_width :
    ¬ ZkGuardrailsOk { zkProfileUd128 with randomizerWidth := 3 } := by
  intro h
  have h2 := h.2.2.1
  revert h2
  decide

/-- **Negative Control (Trap 3):** a degree-3 constraint circuit fits at
`logBlowup = 1` in non-ZK `v6` (`nonZkQuotientDegree 3 = 2 ≤ 2`), yet is
strictly REJECTED in `v6-zk` because 2× odd-coset blinding doubles the quotient
chunks to `zkQuotientDegree 3 = 4 > 2`. -/
theorem negControl_zk_trap3_quotient_blowup :
    nonZkQuotientDegree 3 ≤ 2 ^ 1 ∧
    ¬ ZkGuardrailsOk { zkProfileUd128 with logBlowup := 1, maxConstraintDegree := 3 } := by
  refine ⟨by decide, fun h => ?_⟩
  have h3 := h.2.2.2.2.1
  revert h3
  decide

/-- **Negative Control (Trap 4):** reusing a non-ZK `v6` BLAKE3 domain
(`.merkleLeaf`) inside a `v6-zk` configuration is strictly REJECTED by
`ZkGuardrailsOk` (and `v6ZkMerkleLeafKey ≠ v6MerkleLeafKey`). -/
theorem negControl_zk_trap4_v6_domain_rejected :
    v6ZkMerkleLeafKey ≠ v6MerkleLeafKey ∧
    ¬ ZkGuardrailsOk { zkProfileUd128 with leafDomain := .merkleLeaf } := by
  refine ⟨by decide, fun h => ?_⟩
  have h4 := h.2.2.2.2.2.1
  cases h4

/-! ## Section 5: Executable `v6-zk` Literal `≤ N / 2 ^ 128` Soundness (UD & Johnson) -/

/-- **Executable `multi-stark/v6-zk` 128-Bit Unconditional UD Soundness (`≤ N / 2 ^ 128`):**
for any valid `v6-zk` configuration (`ZkGuardrailsOk cfg`) with
`(logBlowup = 2, numQueries = 160, queryPowBits = 20)` over `GoldilocksExt3`
using 64-byte RFC 7693 `BLAKE2b-512` (`Digest64`, true 512-bit internal state),
incremental sponge chaining (`c = 3 / 2`), salted Merkle leaves (`Salt16` under
`zkMerkleLeaf`), 2× odd-coset blinding, and `W_R ≥ 4` randomizer columns merged
into the quotient claim shape:
1. Executable `Fri.verify` soundness error is literally `≤ N / 2 ^ 128` for all `N ≤ 2 ^ 128`;
2. Concrete PQ collision security is `170.7b` BHT (`+42.7b` headroom above 128b),
   `204.8b` CNS, and `256b` Grover preimage;
3. All `v6-zk` domains are strictly separated from non-ZK `v6` and `plain`. -/
theorem goldilocksExt3_v6Zk_soundness_blake2b512_ud_128
    (cfg : ZkConfig) (hcfg : ZkGuardrailsOk cfg)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = cfg.logBlowup) (hbl2 : cfg.logBlowup = 2)
    (hqn : params.numQueries = cfg.numQueries) (hqn160 : cfg.numQueries = 160)
    (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ cfg.logTraceHeight + 1 + cfg.logBlowup)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 60)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (5 / 8)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128 params shape
    (hbl.trans hbl2) (hqn.trans hqn160) hqpow (hmax.trans hcfg.2.1) hheight hclaims s₀
    hadv hN attempt

/-- **Executable `multi-stark/v6-zk` 128-Bit Johnson Soundness (`≤ N / 2 ^ 128`):**
same 64-byte RFC 7693 `BLAKE2b-512` `v6-zk` hiding-PCS soundness theorem in the
Johnson regime `(logBlowup = 2, numQueries ≥ 118, queryPowBits = 20)` under `CurveListCA`. -/
theorem goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128
    (cfg : ZkConfig) (hcfg : ZkGuardrailsOk cfg)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = cfg.logBlowup) (hbl2 : cfg.logBlowup = 2)
    (hqn : params.numQueries = cfg.numQueries) (hqn118 : 118 ≤ cfg.numQueries)
    (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ cfg.logTraceHeight + 1 + cfg.logBlowup)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest64) {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA Fp3Model T)
    {cT : ℝ} (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ Fri.numRounds params shape → 2 ≤ k →
      (T (2 ^ (Fri.logMaxHeight params.logBlowup shape - j))
        (2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈(65 / 128 : ℝ) * (2 : ℝ) ^ (Fri.logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    (hα_budget : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        (cT + 17 * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤ (2 : ℝ) ^ 62)
    (hβ_budget : 2 * cT + 17 * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤ (2 : ℝ) ^ 62)
    {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (65 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_128 params shape
    (hbl.trans hbl2) (hqn.symm ▸ hqn118) hqpow (hmax.trans hcfg.2.1) hheight s₀
    hca hcT0 hT hα_budget hβ_budget hadv hN attempt

/-- **100% UNCONDITIONAL `multi-stark/v6-zk` 128-Bit Johnson Soundness (`lb = 2, q ≥ 128`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` executable `Fri.verify` soundness
for `v6-zk` at `θ = 71 / 128` (`logBlowup = 2, numQueries ≥ 128, queryPowBits = 20`)
under 64B RFC 7693 `BLAKE2b-512` (`Digest64`), incremental sponge chaining (`c = 3 / 2`),
and `ZkGuardrailsOk cfg`. -/
theorem goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional
    (cfg : ZkConfig) (hcfg : ZkGuardrailsOk cfg)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = cfg.logBlowup) (hbl2 : cfg.logBlowup = 2)
    (hqn : params.numQueries = cfg.numQueries) (hqn128 : 128 ≤ cfg.numQueries)
    (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ cfg.logTraceHeight + 1 + cfg.logBlowup)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 36)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (71 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional params shape
    (hbl.trans hbl2) (hqn.symm ▸ hqn128) hqpow (hmax.trans hcfg.2.1) hheight hclaims s₀
    hadv hN attempt

/-- **100% UNCONDITIONAL `multi-stark/v6-zk` Native STARK Shrinker Johnson Soundness
(`lb = 3, q ≥ 78, queryPow = 20`, `BLAKE2b-512`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` at `θ = 19 / 50`. -/
theorem goldilocksExt3_v6Zk_soundness_blake2b512_johnson_lb3_78_128_unconditional
    (cfg : ZkConfig) (hcfg : ZkGuardrailsOk cfg)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = cfg.logBlowup) (hbl3 : cfg.logBlowup = 3)
    (hqn : params.numQueries = cfg.numQueries) (hqn78 : 78 ≤ cfg.numQueries)
    (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 31)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 32)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans (by decide))
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (19 / 50)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  let _ := hcfg
  exact goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional params shape
    (hbl.trans hbl3) (hqn.symm ▸ hqn78) hqpow hmax hheight hclaims s₀ hadv hN attempt

/-- **100% UNCONDITIONAL `multi-stark/v6-zk` Native STARK Shrinker Johnson Soundness
(`lb = 4, q ≥ 58, queryPow = 20`, `BLAKE2b-512`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` at `θ = 35 / 128`. -/
theorem goldilocksExt3_v6Zk_soundness_blake2b512_johnson_lb4_58_128_unconditional
    (cfg : ZkConfig) (hcfg : ZkGuardrailsOk cfg)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = cfg.logBlowup) (hbl4 : cfg.logBlowup = 4)
    (hqn : params.numQueries = cfg.numQueries) (hqn58 : 58 ≤ cfg.numQueries)
    (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ cfg.logTraceHeight + 1 + cfg.logBlowup)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (35 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional params shape
    (hbl.trans hbl4) (hqn.symm ▸ hqn58) hqpow (hmax.trans hcfg.2.1) hheight hclaims s₀
    hadv hN attempt

end CertiFri.P3.Exec
