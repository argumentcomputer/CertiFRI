import CertiFriProofs.Theory.Domain
import CertiFriProofs.Theory.StepMCA
import CertiFriProofs.Theory.ProximityGap
import CertiFriProofs.Theory.SoundnessCount

/-!
# The low-degree test with no proximity hypothesis

`interactive_soundness` bounds the accepting runs of the low-degree test under
the hypothesis `StepMCAFor` for each folding round. This file discharges that
hypothesis with the elementary proximity gap of `Theory/ProximityGap.lean`, so
the resulting theorems assume nothing about Reed–Solomon codes.

* `stepMCA_of_relDist`, `stepMCAFor_zero_of_relDist`: the proximity hypothesis
  of one folding round, for agreement `1 - δ`. A round in which an input joins
  needs `4 * δ * |D'| + d' ≤ |D'|` and has error `2 * (δ * |D'| + 1) / |F|`; a
  round with no input needs `3 * δ * |D'| + d' ≤ |D'|` and has error
  `(δ * |D'| + 1) / |F|`. Here `D'` is the domain the round folds into and `d'`
  its degree bound.
* `interactive_soundness_of_relDist`: soundness against an adaptive prover for
  an `LdtInstance` whose every round satisfies the first condition.
  `interactive_soundness_of_relDist_single` is the same for a run with a single
  input, under the second condition.
* `twoAdic_interactive_soundness_of_relDist`,
  `twoAdic_interactive_soundness_of_relDist_single`: the two-adic instance in
  Plonky3's parameters, where the rate is `2 ^ (-logBlowup)` at every level.
  The conditions become `4 * δ + (1 / 2) ^ logBlowup ≤ 1` and
  `3 * δ + (1 / 2) ^ logBlowup ≤ 1`, and the challenge errors sum to at most
  `2 * (δ * 2 ^ n + rounds) / |F|` and `(δ * 2 ^ n + rounds) / |F|`.

What is assumed: the model of `Theory/Basic.lean` (committed codewords are
functions, challenges and query points are counted, not sampled), a causal
prover, and a final message that is a codeword. Nothing else.

What is not covered. The radius is small: with rate `ρ`, the theorems reach
relative distance `δ ≤ (1 - ρ) / 4`, or `(1 - ρ) / 3` with a single input, so
`δ < 1 / 4` and `δ < 1 / 3` whatever the blowup. Each query then contributes a
factor `1 - δ > 3 / 4` (`> 2 / 3`) to the bound. The unique-decoding radius
`(1 - ρ) / 2` and the Johnson radius `1 - √ρ` need proximity gaps that are not
proved here; for those, `interactive_soundness` keeps `StepMCAFor` as a
hypothesis. The challenge error is of the order `δ * 2 ^ n / |F|`, so the
bounds say something only when the field is much larger than the first domain.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## One folding round -/

section Step

variable [Fintype F]

/-- The proximity hypothesis of a folding round, whatever input joins, with no
assumption on the code: if `4 * (δ * |D'|) + d' ≤ |D'|`, the round from `D` to
`D'` satisfies `StepMCA` for agreement `1 - δ` with error
`2 * (δ * |D'| + 1) / |F|`. -/
theorem stepMCA_of_relDist {D D' : Finset F} (hstep : SquareStep D D') (d' : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hdist : 4 * (δ * D'.card) + d' ≤ D'.card) :
    StepMCA D D' d' (1 - δ) (2 * (δ * D'.card + 1) / Fintype.card F) :=
  StepMCA.of_curveMCA hstep (curveMCA_three_of_relDist D' d' δ hδ hdist)

/-- The proximity hypothesis of a folding round in which no input joins, with
no assumption on the code: if `3 * (δ * |D'|) + d' ≤ |D'|`, the round from `D`
to `D'` satisfies `StepMCAFor` for the zero input, for agreement `1 - δ` with
error `(δ * |D'| + 1) / |F|`. -/
theorem stepMCAFor_zero_of_relDist {D D' : Finset F} (hstep : SquareStep D D') (d' : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hdist : 3 * (δ * D'.card) + d' ≤ D'.card) :
    StepMCAFor D D' d' (1 - δ) ((δ * D'.card + 1) / Fintype.card F) (fun _ => 0) :=
  StepMCAFor.zero_of_curveMCA hstep (curveMCA_two_of_relDist D' d' δ hδ hdist)

end Step

/-! ## The whole test -/

section Interactive

variable [Fintype F]

open Classical in
/-- Soundness against an adaptive prover with no proximity hypothesis. Let
every round satisfy `4 * (δ * |domain (i + 1)|) + degree (i + 1) ≤
|domain (i + 1)|`. The prover's codewords are a causal function of the
challenges and its final message is always a codeword; some input is not
`(1 - δ)`-close to its code. Then, among all pairs of `rounds` challenges and
`q` query points, the number that make every query accept is at most
`(∑ i, 2 * (δ * |domain (i + 1)| + 1) / |F| + (1 - δ) ^ q) * |F| ^ rounds *
|domain 0| ^ q`. -/
theorem interactive_soundness_of_relDist (S : LdtInstance F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdist : ∀ i < S.rounds,
      4 * (δ * (S.domain (i + 1)).card) + S.degree (i + 1) ≤ (S.domain (i + 1)).card)
    (ro : ℕ → F → F) (c : (ℕ → F) → ℕ → F → F) (hcausal : CausalStrategy c)
    (hfinal : ∀ β, IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c β S.rounds))
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) (1 - δ) (ro i)) (q : ℕ) :
    ((Finset.univ.filter fun p : (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
        QueryAccepts S.rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card : ℝ) ≤
      (∑ i ∈ Finset.range S.rounds, 2 * (δ * (S.domain (i + 1)).card + 1) / Fintype.card F +
          (1 - δ) ^ q) * (Fintype.card F : ℝ) ^ S.rounds * ((S.domain 0).card : ℝ) ^ q :=
  interactive_soundness S
    (ε := fun i => 2 * (δ * (S.domain (i + 1)).card + 1) / Fintype.card F) ro c hcausal hfinal
    (fun i hi => stepMCA_of_relDist (S.step i hi) (S.degree (i + 1)) hδ (hdist i hi) (ro (i + 1)))
    hfar q

open Classical in
/-- Soundness against an adaptive prover for a run with a single input, with no
proximity hypothesis. The inputs of the levels after the first are zero, so
every round is a plain fold, and the condition on each round weakens to
`3 * (δ * |domain (i + 1)|) + degree (i + 1) ≤ |domain (i + 1)|`. If the input
is not `(1 - δ)`-close to its code, the number of pairs of `rounds` challenges
and `q` query points that make every query accept is at most
`(∑ i, (δ * |domain (i + 1)| + 1) / |F| + (1 - δ) ^ q) * |F| ^ rounds *
|domain 0| ^ q`. -/
theorem interactive_soundness_of_relDist_single (S : LdtInstance F) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdist : ∀ i < S.rounds,
      3 * (δ * (S.domain (i + 1)).card) + S.degree (i + 1) ≤ (S.domain (i + 1)).card)
    (ro : ℕ → F → F) (hro : ∀ i < S.rounds, ro (i + 1) = fun _ => 0)
    (c : (ℕ → F) → ℕ → F → F) (hcausal : CausalStrategy c)
    (hfinal : ∀ β, IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c β S.rounds))
    (hfar : ¬ CloseToCode (S.domain 0) (S.degree 0) (1 - δ) (ro 0)) (q : ℕ) :
    ((Finset.univ.filter fun p : (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
        QueryAccepts S.rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card : ℝ) ≤
      (∑ i ∈ Finset.range S.rounds, (δ * (S.domain (i + 1)).card + 1) / Fintype.card F +
          (1 - δ) ^ q) * (Fintype.card F : ℝ) ^ S.rounds * ((S.domain 0).card : ℝ) ^ q :=
  interactive_soundness S
    (ε := fun i => (δ * (S.domain (i + 1)).card + 1) / Fintype.card F) ro c hcausal hfinal
    (fun i hi => by
      rw [hro i hi]
      exact stepMCAFor_zero_of_relDist (S.step i hi) (S.degree (i + 1)) hδ (hdist i hi))
    ⟨0, Nat.zero_le _, hfar⟩ q

end Interactive

/-! ## The two-adic instance in Plonky3's parameters

With `rounds` folding rounds, blowup `2 ^ logBlowup` and a final polynomial of
`2 ^ logFinalPolyLen` coefficients, the first domain has
`2 ^ (rounds + logBlowup + logFinalPolyLen)` points. The instance is
`twoAdicInstance ω n rounds (2 ^ logFinalPolyLen)` with
`n = rounds + logBlowup + logFinalPolyLen`: level `i` has the domain
`twoAdicDomain ω n i` and the degree bound
`2 ^ (rounds - i) * 2 ^ logFinalPolyLen`. -/

namespace Compose

/-- The sizes `2 ^ (n - 1), …, 2 ^ (n - r)` and one more `2 ^ (n - r)` add up
to `2 ^ n`. -/
theorem sum_two_pow_sub_add {n r : ℕ} (hr : r ≤ n) :
    ∑ i ∈ Finset.range r, 2 ^ (n - (i + 1)) + 2 ^ (n - r) = 2 ^ n := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : n - r = n - (r + 1) + 1 := by omega
    rw [Finset.sum_range_succ, add_assoc, ← two_mul, ← pow_succ', ← h]
    exact ih (by omega)

section TwoAdic

variable [DecidableEq F] {ω : F} {n rounds logBlowup logFinalPolyLen : ℕ}

/-- The domains that the first `r` rounds fold into have fewer than `2 ^ n`
points in total. -/
theorem sum_card_twoAdicDomain_le (hω : IsPrimitiveRoot ω (2 ^ n)) {r : ℕ} (hr : r ≤ n) :
    ∑ i ∈ Finset.range r, (twoAdicDomain ω n (i + 1)).card ≤ 2 ^ n := by
  rw [← sum_two_pow_sub_add hr]
  refine le_add_right (Finset.sum_le_sum fun i hi => ?_)
  rw [card_twoAdicDomain hω (by have := Finset.mem_range.mp hi; omega)]

/-- The challenge errors of the first `r` rounds, without the factor
`1 / |F|`, add up to at most `δ * 2 ^ n + r`. -/
theorem sum_error_twoAdicDomain_le (hω : IsPrimitiveRoot ω (2 ^ n)) {r : ℕ} (hr : r ≤ n) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    ∑ i ∈ Finset.range r, (δ * (twoAdicDomain ω n (i + 1)).card + 1) ≤ δ * 2 ^ n + r := by
  have h : (∑ i ∈ Finset.range r, ((twoAdicDomain ω n (i + 1)).card : ℝ)) ≤ 2 ^ n := by
    exact_mod_cast sum_card_twoAdicDomain_le hω hr
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  gcongr

/-- In Plonky3's parameters every level has rate `2 ^ (-logBlowup)`: the domain
of level `i` is `2 ^ logBlowup` times as large as the degree bound. -/
theorem card_twoAdicDomain_eq_mul_degree (hn : n = rounds + logBlowup + logFinalPolyLen)
    (hω : IsPrimitiveRoot ω (2 ^ n)) {i : ℕ} (hi : i ≤ rounds) :
    (twoAdicDomain ω n i).card = 2 ^ logBlowup * (2 ^ (rounds - i) * 2 ^ logFinalPolyLen) := by
  rw [card_twoAdicDomain hω (by omega), ← pow_add, ← pow_add]
  congr 1
  omega

/-- In Plonky3's parameters the distance condition of a level follows from a
condition on the rate: if `a * δ + (1 / 2) ^ logBlowup ≤ 1`, then
`a * (δ * |domain i|) + degree i ≤ |domain i|` at every level `i ≤ rounds`. -/
theorem twoAdic_relDist (hn : n = rounds + logBlowup + logFinalPolyLen)
    (hω : IsPrimitiveRoot ω (2 ^ n)) {a δ : ℝ} (h : a * δ + (1 / 2) ^ logBlowup ≤ 1) {i : ℕ}
    (hi : i ≤ rounds) :
    a * (δ * (twoAdicDomain ω n i).card) + (2 ^ (rounds - i) * 2 ^ logFinalPolyLen : ℕ) ≤
      (twoAdicDomain ω n i).card := by
  rw [card_twoAdicDomain_eq_mul_degree hn hω hi]
  push_cast
  have hX : (0 : ℝ) ≤ 2 ^ logBlowup * (2 ^ (rounds - i) * 2 ^ logFinalPolyLen) := by positivity
  have h1 : (1 / 2 : ℝ) ^ logBlowup * 2 ^ logBlowup = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 : (1 / 2 : ℝ) ^ logBlowup * (2 ^ logBlowup * (2 ^ (rounds - i) * 2 ^ logFinalPolyLen)) =
      2 ^ (rounds - i) * 2 ^ logFinalPolyLen := by rw [← mul_assoc, h1, one_mul]
  have key := mul_le_mul_of_nonneg_right h hX
  linarith

end TwoAdic

end Compose

section TwoAdic

variable [Fintype F] [DecidableEq F] {ω : F} {n rounds logBlowup logFinalPolyLen : ℕ}

open Classical in
/-- Soundness of the low-degree test in Plonky3's parameters, with no proximity
hypothesis. The test has `rounds` folding rounds, blowup `2 ^ logBlowup` and a
final polynomial of degree below `2 ^ logFinalPolyLen`; its domains are the
two-adic subgroups of `ω`, a primitive `2 ^ n`-th root of unity with
`n = rounds + logBlowup + logFinalPolyLen`. Let `4 * δ + (1 / 2) ^ logBlowup ≤ 1`.
The prover's codewords are a causal function of the challenges and its final
message always has degree below `2 ^ logFinalPolyLen`; some input is not
`(1 - δ)`-close to its code. Then, among all pairs of `rounds` challenges and
`q` query points, the number that make every query accept is at most
`(2 * (δ * 2 ^ n + rounds) / |F| + (1 - δ) ^ q) * |F| ^ rounds * (2 ^ n) ^ q`.

This is `interactive_soundness_of_relDist` for
`twoAdicInstance ω n rounds (2 ^ logFinalPolyLen)`, with its domains and degree
bounds written out. -/
theorem twoAdic_interactive_soundness_of_relDist
    (hn : n = rounds + logBlowup + logFinalPolyLen) (hω : IsPrimitiveRoot ω (2 ^ n)) {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 4 * δ + (1 / 2) ^ logBlowup ≤ 1)
    (ro : ℕ → F → F) (c : (ℕ → F) → ℕ → F → F) (hcausal : CausalStrategy c)
    (hfinal : ∀ β, IsCodeword (twoAdicDomain ω n rounds) (2 ^ logFinalPolyLen) (c β rounds))
    (hfar : ∃ i ≤ rounds, ¬ CloseToCode (twoAdicDomain ω n i)
      (2 ^ (rounds - i) * 2 ^ logFinalPolyLen) (1 - δ) (ro i)) (q : ℕ) :
    ((Finset.univ.filter fun p : (Fin rounds → F) × (Fin q → ↥(twoAdicDomain ω n 0)) => ∀ t,
        QueryAccepts rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card : ℝ) ≤
      (2 * (δ * 2 ^ n + rounds) / Fintype.card F + (1 - δ) ^ q) *
        (Fintype.card F : ℝ) ^ rounds * ((2 : ℝ) ^ n) ^ q := by
  have hr : rounds ≤ n := by omega
  have h := interactive_soundness_of_relDist
    (twoAdicInstance ω n rounds (2 ^ logFinalPolyLen) hω hr) hδ
    (fun i hi => Compose.twoAdic_relDist hn hω hrate (i := i + 1) hi) ro c hcausal
    (fun β => by simpa using hfinal β) hfar q
  refine h.trans ?_
  have hsum := Compose.sum_error_twoAdicDomain_le hω hr hδ
  simp only [twoAdicInstance_rounds, twoAdicInstance_domain, card_twoAdicDomain hω (Nat.zero_le n),
    Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat, ← Finset.sum_div, ← Finset.mul_sum]
  gcongr

open Classical in
/-- Soundness of the low-degree test in Plonky3's parameters for a run with a
single input, with no proximity hypothesis. The setting is that of
`twoAdic_interactive_soundness_of_relDist`, but the inputs of the levels after
the first are zero. Then `3 * δ + (1 / 2) ^ logBlowup ≤ 1` suffices: if the
input is not `(1 - δ)`-close to the code of degree below
`2 ^ rounds * 2 ^ logFinalPolyLen` on the first domain, the number of pairs of
`rounds` challenges and `q` query points that make every query accept is at
most `((δ * 2 ^ n + rounds) / |F| + (1 - δ) ^ q) * |F| ^ rounds * (2 ^ n) ^ q`. -/
theorem twoAdic_interactive_soundness_of_relDist_single
    (hn : n = rounds + logBlowup + logFinalPolyLen) (hω : IsPrimitiveRoot ω (2 ^ n)) {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 3 * δ + (1 / 2) ^ logBlowup ≤ 1)
    (ro : ℕ → F → F) (hro : ∀ i < rounds, ro (i + 1) = fun _ => 0)
    (c : (ℕ → F) → ℕ → F → F) (hcausal : CausalStrategy c)
    (hfinal : ∀ β, IsCodeword (twoAdicDomain ω n rounds) (2 ^ logFinalPolyLen) (c β rounds))
    (hfar : ¬ CloseToCode (twoAdicDomain ω n 0) (2 ^ rounds * 2 ^ logFinalPolyLen) (1 - δ)
      (ro 0)) (q : ℕ) :
    ((Finset.univ.filter fun p : (Fin rounds → F) × (Fin q → ↥(twoAdicDomain ω n 0)) => ∀ t,
        QueryAccepts rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card : ℝ) ≤
      ((δ * 2 ^ n + rounds) / Fintype.card F + (1 - δ) ^ q) *
        (Fintype.card F : ℝ) ^ rounds * ((2 : ℝ) ^ n) ^ q := by
  have hr : rounds ≤ n := by omega
  have h := interactive_soundness_of_relDist_single
    (twoAdicInstance ω n rounds (2 ^ logFinalPolyLen) hω hr) hδ
    (fun i hi => Compose.twoAdic_relDist hn hω hrate (i := i + 1) hi) ro hro c hcausal
    (fun β => by simpa using hfinal β) hfar q
  refine h.trans ?_
  have hsum := Compose.sum_error_twoAdicDomain_le hω hr hδ
  simp only [twoAdicInstance_rounds, twoAdicInstance_domain, card_twoAdicDomain hω (Nat.zero_le n),
    Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat, ← Finset.sum_div]
  gcongr

end TwoAdic

end CertiFri
