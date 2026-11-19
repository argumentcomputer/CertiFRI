import CertiFriProofs.Theory.PcsRbr

/-!
# Grinding

Plonky3 precedes some challenges with a proof-of-work check. The prover's
message carries a witness; the verifier absorbs it, samples `b` bits, rejects
unless they are all zero (`check_witness`), and then samples the challenge from
the same challenger state. This file adds the check to any public-coin protocol
with a state function, and then to the whole check of `Theory/PcsRbr.lean`.

## The model

The challenge of a round with a check of `b` bits is a pair
`(w, c) : Fin (2 ^ b) × C`: the sampled bits, as a number, and the challenge of
the round. In the Fiat–Shamir transformation of `Theory/Oracle/FiatShamir.lean`
the pair is one answer of the random oracle, to the transcript so far and the
new message. The witness is part of that message in the compiled protocol; the
messages of this file do not show it.

* `GrindChal bits C i` is `Fin (2 ^ bits i) × C i`. A round without a check has
  `bits i = 0`.
* `ungrind t` is the transcript `t` without the samples, and `PowPasses t` says
  that every sample of `t` is zero.
* `grindDoomed bits doomed i t`: the transcript is doomed when one of its
  samples is not zero, or when `ungrind t` is doomed. After a failed check the
  transcript stays doomed whatever follows, as the verifier rejects.

## Results

* `rbrSound_grindDoomed`, for any protocol: if `doomed` is round-by-round sound
  with nonnegative errors `ε`, then `grindDoomed bits doomed` is round-by-round
  sound with the errors `ε i / 2 ^ bits i`. The errors have to be nonnegative
  because a transcript with a failed check is doomed for every next challenge.
* `rbrSound_grind`: the whole check with proof of work. Under the hypotheses of
  `rbrSound`, the state function `grindDoomed bits (doomed S s θ q)` is
  round-by-round sound with the errors `roundError S.rounds εα εβ θ q i / 2 ^ bits i`.
* `not_grindDoomed_of_accepts`: a full transcript whose checks pass, whose
  claims fail and on which the verifier accepts is not doomed.
  `grindDoomed_nil`: the empty transcript is doomed.
* `ungrind_mapIdx`, `powPasses_mapIdx`: dropping the samples and reading the
  messages through an interpretation commute.

## Correspondence with Plonky3

In `verify_fri` (`fri/src/verifier.rs`), with `R = S.rounds` folding rounds:

* `alpha` is sampled without a check, so `bits 0 = 0`;
* each folding challenge is sampled after
  `check_witness(params.commit_proof_of_work_bits, witness)`, so
  `bits (1 + i) = commit_proof_of_work_bits` for `i < R`;
* the query indices are sampled after
  `check_witness(params.query_proof_of_work_bits, proof.query_pow_witness)`, so
  `bits (R + 1) = query_proof_of_work_bits`.

The errors are then `∑ j ∈ range (R + 1), εα j` for `α`,
`εβ i / 2 ^ commit_proof_of_work_bits` for folding round `i`, and
`θ ^ q / 2 ^ query_proof_of_work_bits` for the queries.

## Not modeled

* The sampled bits are uniform here. Plonky3's `sample_bits` takes the low bits
  of a uniform element of a prime field of order `p`, so each value has a
  probability within `1 / p` of `1 / 2 ^ b`.
* The bits and the challenge are independent here, as two parts of one answer
  of a random oracle. In Plonky3 they are successive outputs of one sponge.
* The prover's search for a witness. Only the verifier's check appears.
-/

namespace CertiFri.PcsRbr

open Oracle

universe u v w

/-! ## Proof of work in a public-coin protocol -/

section Generic

variable {M : Type u} {M' : Type w} {C : ℕ → Type v} {bits : ℕ → ℕ}

/-- The challenge type of a round with a proof-of-work check of `bits i` bits:
the sampled bits, as a number below `2 ^ bits i`, and the challenge of the
round. With `bits i = 0` the first component carries nothing. -/
abbrev GrindChal (bits : ℕ → ℕ) (C : ℕ → Type v) (i : ℕ) : Type v :=
  Fin (2 ^ bits i) × C i

/-- The challenge types with proof of work are nonempty when the challenge
types are. -/
instance [∀ i, Nonempty (C i)] (i : ℕ) : Nonempty (GrindChal bits C i) :=
  ⟨⟨⟨0, Nat.two_pow_pos _⟩, Classical.arbitrary _⟩⟩

/-- The transcript without the proof-of-work samples. -/
def ungrind : {i : ℕ} → Transcript M (GrindChal bits C) i → Transcript M C i
  | _, .nil => .nil
  | _, .snoc t m c => (ungrind t).snoc m c.2

/-- Every proof-of-work check of the transcript passes: the sampled bits of
every round are all zero. -/
def PowPasses : {i : ℕ} → Transcript M (GrindChal bits C) i → Prop
  | _, .nil => True
  | _, .snoc t _ c => PowPasses t ∧ (c.1 : ℕ) = 0

/-- The state function of a protocol with proof of work: a transcript is doomed
when one of its proof-of-work checks fails, or it is doomed without its
proof-of-work samples. -/
def grindDoomed (bits : ℕ → ℕ) (doomed : ∀ i, Transcript M C i → Prop) (i : ℕ)
    (t : Transcript M (GrindChal bits C) i) : Prop :=
  PowPasses t → doomed i (ungrind t)

/-- `ungrind` of an extended transcript. -/
@[simp] theorem ungrind_snoc {i : ℕ} (t : Transcript M (GrindChal bits C) i) (m : M)
    (c : GrindChal bits C i) : ungrind (t.snoc m c) = (ungrind t).snoc m c.2 := rfl

/-- The checks of an extended transcript pass when the earlier ones do and the
new sample is zero. -/
@[simp] theorem powPasses_snoc {i : ℕ} (t : Transcript M (GrindChal bits C) i) (m : M)
    (c : GrindChal bits C i) : PowPasses (t.snoc m c) ↔ PowPasses t ∧ (c.1 : ℕ) = 0 := Iff.rfl

/-- Dropping the samples commutes with reading the messages differently. -/
theorem ungrind_mapIdx (f : ℕ → M → M') :
    ∀ {i : ℕ} (t : Transcript M (GrindChal bits C) i),
      ungrind (t.mapIdx f) = (ungrind t).mapIdx f
  | _, .nil => rfl
  | _, .snoc t m c => by
    rw [Transcript.mapIdx_snoc, ungrind_snoc, ungrind_snoc, Transcript.mapIdx_snoc,
      ungrind_mapIdx f t]

/-- Whether the checks pass does not depend on how the messages are read. -/
theorem powPasses_mapIdx (f : ℕ → M → M') :
    ∀ {i : ℕ} (t : Transcript M (GrindChal bits C) i), PowPasses (t.mapIdx f) ↔ PowPasses t
  | _, .nil => Iff.rfl
  | _, .snoc t m c => by
    rw [Transcript.mapIdx_snoc, powPasses_snoc, powPasses_snoc, powPasses_mapIdx f t]

/-- The empty transcript is doomed with proof of work if it is without. -/
theorem grindDoomed_nil {doomed : ∀ i, Transcript M C i → Prop} (h : doomed 0 .nil) :
    grindDoomed bits doomed 0 .nil :=
  fun _ => h

/-- A transcript whose checks pass and which is not doomed without its samples
is not doomed. -/
theorem not_grindDoomed {doomed : ∀ i, Transcript M C i → Prop} {i : ℕ}
    {t : Transcript M (GrindChal bits C) i} (hpow : PowPasses t)
    (h : ¬ doomed i (ungrind t)) : ¬ grindDoomed bits doomed i t :=
  fun hd => h (hd hpow)

/-- **Proof of work divides the error.** If `doomed` is round-by-round sound
with nonnegative errors `ε`, then with a proof-of-work check of `bits i` bits
in round `i` the state function `grindDoomed bits doomed` is round-by-round
sound with the errors `ε i / 2 ^ bits i`. -/
theorem rbrSound_grindDoomed [∀ i, Fintype (C i)] {r : ℕ}
    {doomed : ∀ i, Transcript M C i → Prop} {ε : ℕ → ℝ} (h : RbrSound r doomed ε)
    (hε : ∀ i < r, 0 ≤ ε i) (bits : ℕ → ℕ) :
    RbrSound r (grindDoomed bits doomed) (fun i => ε i / 2 ^ bits i) := by
  intro i hi t m hd
  have hpow : (0 : ℝ) < 2 ^ bits i := by positivity
  by_cases hp : PowPasses t
  · obtain ⟨B, hB, hmem⟩ := h i hi (ungrind t) m (hd hp)
    refine ⟨B.map ⟨fun c => (⟨0, Nat.two_pow_pos _⟩, c), fun a b hab => (Prod.ext_iff.mp hab).2⟩,
      ?_, ?_⟩
    · rw [Finset.card_map, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, div_mul_eq_mul_div, ← mul_assoc, mul_comm (ε i), mul_assoc,
        mul_div_cancel_left₀ _ hpow.ne']
      exact hB
    · rintro ⟨w, c⟩ hnd
      have hw : (w : ℕ) = 0 := by
        by_contra hw
        exact hnd fun hpp => absurd hpp.2 hw
      exact Finset.mem_map.mpr ⟨c, hmem c fun hdd => hnd fun _ => hdd,
        Prod.ext (Fin.ext hw.symm) rfl⟩
  · exact (FractionLE.false.mono_right (div_nonneg (hε i hi) hpow.le)).mono_left
      fun c hnd => hnd fun hpp => absurd hpp.1 hp

end Generic

/-! ## The whole check with proof of work -/

section Pcs

variable {F : Type u} [Field F] [DecidableEq F] {m : ℕ → ℕ}

/-- **Round-by-round soundness of the whole check with proof of work.** Under
the hypotheses of `rbrSound`, with a proof-of-work check of `bits i` bits in
round `i`, the state function `grindDoomed bits (doomed S s θ q)` is
round-by-round sound, and the error of round `i` is that of `rbrSound` divided
by `2 ^ bits i`. -/
theorem rbrSound_grind [Fintype F] (S : LdtInstance F) {s : F} (hs : s ≠ 0) {θ : ℝ}
    (hθ : 0 ≤ θ) (q : ℕ) {εα εβ : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (εβ i))
    (bits : ℕ → ℕ) :
    RbrSound (S.rounds + 2) (grindDoomed bits (doomed S s θ q (m := m)))
      (fun i => roundError S.rounds εα εβ θ q i / 2 ^ bits i) :=
  rbrSound_grindDoomed (rbrSound S hs hθ q hmca hstep)
    (fun i _ => roundError_nonneg S hθ q hmca hstep i) bits

/-- The final event with proof of work. A full transcript whose proof-of-work
checks pass, whose claims fail, and on which the verifier accepts is not
doomed. -/
theorem not_grindDoomed_of_accepts {S : LdtInstance F} {s : F} {θ : ℝ} {q : ℕ} {bits : ℕ → ℕ}
    (t : Transcript (Msg F m) (GrindChal bits (Chal S q)) (S.rounds + 2)) (hpow : PowPasses t)
    (hfail : ClaimsFail S s θ (claimsOf (ungrind t))) (hacc : Accepts S s (ungrind t)) :
    ¬ grindDoomed bits (doomed S s θ q) (S.rounds + 2) t :=
  not_grindDoomed hpow (not_doomed_of_accepts (ungrind t) hfail hacc)

end Pcs

end CertiFri.PcsRbr
