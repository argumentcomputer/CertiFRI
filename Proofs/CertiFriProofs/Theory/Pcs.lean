import CertiFriProofs.Theory.Domain
import CertiFriProofs.Theory.SoundnessCount
import CertiFriProofs.Theory.Quotient

/-!
# From the low-degree test to the evaluation claims

The verifier is a polynomial commitment verifier. It receives evaluation
claims, draws one challenge `α`, forms for each height the reduced opening of
the claims of that height (`reducedOpening`, a function on the coset
`s * H_j`), and runs the low-degree test on the subgroups `H_j` with the
reduced openings as inputs. This file composes the two halves: the quotient
argument of `Theory/Quotient.lean`, which turns closeness of a reduced opening
into claims, and the soundness of the low-degree test of
`Theory/SoundnessCount.lean`.

## The model

`S : LdtInstance F` holds the subgroups `S.domain j` and the degree bounds
`S.degree j`; level `j` is the domain after `j` folds. `s ≠ 0` is the coset
shift, the same at every level, so the coset of level `j` is
`(S.domain j).image (s * ·)`. Level `j` has `m j` claims, `claims j`. A level
with no claims has `m j = 0`, and its input is zero (`pcsInput_eq_zero`).

* `ClaimsHold D d θ claims`: there is a set holding a fraction `θ` of `D` on
  which every claimed function agrees with a polynomial of degree at most `d`
  that takes the claimed value at the claimed point. True claims hold
  (`ClaimsHold.of_eval`). A wrong value claimed for a function that is a
  polynomial of degree at most `d` on `D` makes the claims fail, as soon as
  `d < θ * |D|` (`not_claimsHold_of_eval_ne`).
* `pcsInput s claims α j`: the input of level `j` of the low-degree test, the
  reduced opening of `claims j` on the coset, read on the subgroup.

## Results

* `claimsHold_of_pcsInput`, the `α` round. For all but a
  `∑ j ∈ range (rounds + 1), εα j` fraction of `α`: at every level, if the
  input is `θ`-close to its code, the claims of that level hold.
* `pcs_interactive_soundness`, the whole check. The prover chooses its
  codewords after seeing `α` and the earlier folding challenges. If the claims
  fail at some level, then among all triples of a value of `α`, `rounds`
  folding challenges and `q` query points, the number that make every query
  accept is at most
  `(∑ j, εα j + ∑ i, ε i + θ ^ q) * |F| ^ (rounds + 1) * |domain 0| ^ q`.
  There are `|F| ^ (rounds + 1) * |domain 0| ^ q` triples.
* `PcsDoomed` and `PcsDoomed.card_escape_le`, the `α` round in the round-by-round
  form described next.

## The state function

For a Fiat–Shamir analysis the bound splits into one bound per verifier
message. A partial transcript is *doomed* when

* before `α`: `PcsDoomed S s θ claims`, the claims fail at some level;
* after `α`: `S.Doomed θ (pcsInput s claims α) c β 0`, some input is not
  `θ`-close to its code;
* after `k` folding rounds: `S.Doomed θ (pcsInput s claims α) c β k`, some
  input is not `θ`-close and the first `k` folding challenges were good.

Each verifier message leaves the doomed state for few of its values:

* `PcsDoomed.card_escape_le`: from `PcsDoomed S s θ claims`, at most
  `(∑ j ∈ range (rounds + 1), εα j) * |F|` values of `α` lead to a state that
  is not `S.Doomed θ (pcsInput s claims α) c β 0`.
* `LdtInstance.Doomed.card_escape_le`: from `S.Doomed θ ro c β k`, whatever
  codeword `c k` the prover commits to, at most `ε k * |F|` values of the
  challenge `β k` lead to a state that is not `S.Doomed θ ro c β (k + 1)`.
* `LdtInstance.Doomed.card_accepting_queries_le`: in the state
  `S.Doomed θ ro c β S.rounds`, if the final message is a codeword, at most
  `(θ * |domain 0|) ^ q` of the `q`-tuples of query points all accept.

The last two are in `Theory/SoundnessCount.lean`; here they are used with
`ro = pcsInput s claims α`. The second asks for `StepMCAFor` with the input
`pcsInput s claims α (k + 1)`, which `StepMCA` for round `k` provides.

## Assumptions

* `CurveMCA` on the coset of each level, for curves with `m j` terms, with
  error `εα j`. It is a hypothesis throughout. The elementary proximity gap of
  `Theory/ProximityGap.lean` reaches relative distance `(1 - ρ) / (m + 1)` for
  `m` terms, which shrinks to nothing as the number of claims grows, so it
  gives no useful instance for the `α` round. A level with no claims, or with
  one, satisfies the hypothesis with error zero (`Compose.curveMCA_zero`,
  `Compose.curveMCA_one`).
* `StepMCA` for each folding round, for every input, since the inputs depend on
  `α`. For `θ = 1 - δ` in the elementary regime, `stepMCA_of_relDist` of
  `Theory/Unconditional.lean` proves it.
* No opening point lies in the coset of its level (`hz`).
* The claims are fixed before `α` is drawn: the exceptional set of `α` depends
  on them. The prover's codewords may depend on `α`.

## Not modeled, not covered

* Merkle commitments and Fiat–Shamir. The claimed functions and the prover's
  codewords are functions the verifier reads, and the bounds count values of
  `α`, of the folding challenges and of the query points; no hash function and
  no probability space appears.
* The map from the verifier's query indices to coset points. A query is a
  point `x` of `S.domain 0`, and the input of level `j` is read at
  `s * x ^ 2 ^ j`.
* Plonky3's check that the reduced opening at height `log_blowup` is zero, and
  its rejection of inputs whose height the fold never reaches. The model has
  inputs at the levels `0, …, S.rounds` only.
* Grinding (the proof-of-work checks).
* The exact degree. The conclusion gives polynomials of degree at most
  `S.degree j`, one more than an honest polynomial has: the test bounds the
  degree of the quotient, and the quotient of an honest polynomial has a
  degree one lower than the bound.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Claims and inputs -/

/-- On a set of density `θ`, every claimed function agrees with a polynomial of
degree at most `d` that takes the claimed value at the claimed point. The set
is common to all the claims. -/
def ClaimsHold (D : Finset F) (d : ℕ) (θ : ℝ) {m : ℕ} (claims : Fin m → Claim F) : Prop :=
  ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ k, ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
    P.eval (claims k).z = (claims k).y ∧ ∀ x ∈ B, (claims k).f x = P.eval x

/-- The input of level `j` of the low-degree test: the reduced opening on the
coset, read on the subgroup. -/
def pcsInput (s : F) {m : ℕ → ℕ} (claims : ∀ j, Fin (m j) → Claim F) (α : F) (j : ℕ) (x : F) : F :=
  reducedOpening α (claims j) (s * x)

/-- A level with no claims has the zero input. -/
theorem pcsInput_eq_zero (s : F) {m : ℕ → ℕ} (claims : ∀ j, Fin (m j) → Claim F) (α : F) {j : ℕ}
    (hj : m j = 0) : pcsInput s claims α j = fun _ => 0 := by
  have : IsEmpty (Fin (m j)) := by
    rw [hj]
    infer_instance
  funext x
  simp [pcsInput, reducedOpening]

/-- True claims hold: if every claimed function is, on all of `D`, a polynomial
of degree at most `d` that takes the claimed value at the claimed point, the
claims hold for every `θ ≤ 1`. -/
theorem ClaimsHold.of_eval {D : Finset F} {d : ℕ} {θ : ℝ} (hθ : θ ≤ 1) {m : ℕ}
    {claims : Fin m → Claim F}
    (h : ∀ k, ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧ P.eval (claims k).z = (claims k).y ∧
      ∀ x ∈ D, (claims k).f x = P.eval x) : ClaimsHold D d θ claims :=
  ⟨D, Finset.Subset.refl D, by nlinarith [(Nat.cast_nonneg D.card : (0 : ℝ) ≤ D.card)], h⟩

/-- When `θ * |D| ≤ 0` all claims hold: the empty set is large enough. -/
theorem ClaimsHold.of_nonpos {D : Finset F} {θ : ℝ} (h : θ * D.card ≤ 0) (d : ℕ) {m : ℕ}
    (claims : Fin m → Claim F) : ClaimsHold D d θ claims :=
  ⟨∅, Finset.empty_subset D, by simpa using h, fun k =>
    ⟨C (claims k).y, degree_C_le.trans_lt (by exact_mod_cast Nat.succ_pos d), eval_C,
      fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩

/-- A wrong value makes the claims fail. Let the function of claim `k` be, on
all of `D`, a polynomial `P` of degree at most `d` whose value at the claimed
point is not the claimed value. If a set of density `θ` has more than `d`
points, the claims do not hold. -/
theorem not_claimsHold_of_eval_ne {D : Finset F} {d : ℕ} {θ : ℝ} {m : ℕ}
    {claims : Fin m → Claim F} {k : Fin m} {P : F[X]} (hP : P.degree < (d + 1 : ℕ))
    (hf : ∀ x ∈ D, (claims k).f x = P.eval x) (hy : P.eval (claims k).z ≠ (claims k).y)
    (hθ : (d : ℝ) < θ * D.card) : ¬ ClaimsHold D d θ claims := by
  rintro ⟨B, hBD, hB, h⟩
  obtain ⟨Q, hQ, hQz, hQB⟩ := h k
  have hcard : d + 1 ≤ B.card := by exact_mod_cast hθ.trans_le hB
  have hPQ : P = Q := eq_of_degrees_lt_of_eval_finset_eq B
    (hP.trans_le (by exact_mod_cast hcard)) (hQ.trans_le (by exact_mod_cast hcard))
    fun x hx => by rw [← hf x (hBD hx), hQB x hx]
  exact hy (hPQ ▸ hQz)

/-! ## Easy facts about the proximity hypotheses -/

namespace Compose

/-- A level with no claims: `CurveMCA` for curves with no terms holds with
error zero. -/
theorem curveMCA_zero [Fintype F] (D : Finset F) (d : ℕ) (θ : ℝ) : CurveMCA D d 0 θ 0 :=
  fun _ => ⟨∅, by simp, fun _ _ _ _ _ _ _ _ => ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0⟩⟩

/-- A level with one claim: `CurveMCA` for curves with one term holds with error
zero, since the curve is its only term. -/
theorem curveMCA_one [Fintype F] (D : Finset F) (d : ℕ) (θ : ℝ) : CurveMCA D d 1 θ 0 := by
  refine fun u => ⟨∅, by simp, fun β _ p hp B _ _ h => ⟨fun _ => p, fun _ => hp, fun k x hx => ?_⟩⟩
  have hk : k = 0 := Subsingleton.elim k 0
  simpa [hk] using h x hx

/-- The error of a round that satisfies `StepMCA` is nonnegative. -/
theorem nonneg_of_stepMCA [Fintype F] {D D' : Finset F} {d' : ℕ} {θ ε : ℝ}
    (h : StepMCA D D' d' θ ε) : 0 ≤ ε := by
  obtain ⟨bad, hbad, -⟩ := h (fun _ => 0) (fun _ => 0)
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg bad.card).trans hbad) hF

end Compose

/-! ## The `α` round -/

/-- The `α` round. Assume `CurveMCA` on the coset of every level, with error
`εα j` at level `j`, and that no opening point lies in the coset of its level.
Then for all but a `∑ j ∈ range (rounds + 1), εα j` fraction of `α`: at every
level `j`, if the input of the low-degree test is `θ`-close to its code on the
subgroup, the claims of level `j` hold on the coset. -/
theorem claimsHold_of_pcsInput [Fintype F] [DecidableEq F] (S : LdtInstance F) {s : F}
    (hs : s ≠ 0) {m : ℕ → ℕ} {θ : ℝ} {εα : ℕ → ℝ} (claims : ∀ j, Fin (m j) → Claim F)
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (hz : ∀ j ≤ S.rounds, ∀ k, (claims j k).z ∉ (S.domain j).image (s * ·)) :
    ∃ bad : Finset F,
      (bad.card : ℝ) ≤ (∑ j ∈ Finset.range (S.rounds + 1), εα j) * Fintype.card F ∧
      ∀ α ∉ bad, ∀ j ≤ S.rounds,
        CloseToCode (S.domain j) (S.degree j) θ (pcsInput s claims α j) →
        ClaimsHold ((S.domain j).image (s * ·)) (S.degree j) θ (claims j) := by
  have hmem : ∀ j ∈ Finset.range (S.rounds + 1), j ≤ S.rounds := fun j hj =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨bad, hbad, h⟩ := claims_of_reducedOpening_heights (Finset.range (S.rounds + 1))
    (D := fun j => (S.domain j).image (s * ·)) (d := S.degree) (ε := εα)
    (fun j hj => hmca j (hmem j hj)) claims (fun j hj => hz j (hmem j hj))
  exact ⟨bad, hbad, fun α hα j hj hclose =>
    h α hα j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
      ((closeToCode_image_mul hs (S.domain j) (S.degree j) θ _).mpr hclose)⟩

/-! ## The state before `α` -/

/-- The doomed state before `α` is drawn: the claims fail at some level. -/
def PcsDoomed [DecidableEq F] (S : LdtInstance F) (s : F) (θ : ℝ) {m : ℕ → ℕ}
    (claims : ∀ j, Fin (m j) → Claim F) : Prop :=
  ∃ j ≤ S.rounds, ¬ ClaimsHold ((S.domain j).image (s * ·)) (S.degree j) θ (claims j)

/-- If the claims fail at some level, `θ` is positive. -/
theorem PcsDoomed.pos [DecidableEq F] {S : LdtInstance F} {s : F} {θ : ℝ} {m : ℕ → ℕ}
    {claims : ∀ j, Fin (m j) → Claim F} (h : PcsDoomed S s θ claims) : 0 < θ := by
  obtain ⟨j, -, hj⟩ := h
  by_contra hθ
  exact hj (ClaimsHold.of_nonpos
    (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hθ) (Nat.cast_nonneg _)) _ _)

open Classical in
/-- The `α` round of a doomed transcript. If the claims fail at some level, at
most `(∑ j ∈ range (rounds + 1), εα j) * |F|` values of `α` lead to a state
that is not doomed for the low-degree test, that is, to inputs that are all
`θ`-close to their codes.

The state after `α` does not depend on the codewords or the folding challenges
(`LdtInstance.doomed_zero_iff`), so `c` and `β` are arbitrary here and may
depend on `α`. -/
theorem PcsDoomed.card_escape_le [Fintype F] [DecidableEq F] {S : LdtInstance F} {s : F}
    {θ : ℝ} {m : ℕ → ℕ} {claims : ∀ j, Fin (m j) → Claim F} (h : PcsDoomed S s θ claims)
    (hs : s ≠ 0) {εα : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (hz : ∀ j ≤ S.rounds, ∀ k, (claims j k).z ∉ (S.domain j).image (s * ·))
    (c : F → ℕ → F → F) (β : F → ℕ → F) :
    ((Finset.univ.filter fun α : F =>
        ¬ S.Doomed θ (pcsInput s claims α) (c α) (β α) 0).card : ℝ) ≤
      (∑ j ∈ Finset.range (S.rounds + 1), εα j) * Fintype.card F := by
  obtain ⟨bad, hbad, hgood⟩ := claimsHold_of_pcsInput S hs claims hmca hz
  obtain ⟨j, hj, hfail⟩ := h
  refine le_trans ?_ hbad
  exact_mod_cast Finset.card_le_card fun α hα => by
    by_contra hmem
    exact (Finset.mem_filter.mp hα).2 ((S.doomed_zero_iff θ _ _ _).mpr
      ⟨j, hj, fun hclose => hfail (hgood α hmem j hj hclose)⟩)

/-! ## The whole check -/

open Classical in
/-- Soundness of the whole check against an adaptive prover, as a count.

The claims are fixed. The prover's codewords `c α β` are, for each `α`, a
causal function of the folding challenges, and its final message is always a
codeword. Assume `CurveMCA` on the coset of every level with error `εα j`,
that no opening point lies in the coset of its level, and `StepMCA` for every
folding round with error `ε i`. If the claims fail at some level, then among
all triples of a value of `α`, `rounds` folding challenges and `q` query
points, the number that make every query accept is at most
`(∑ j, εα j + ∑ i, ε i + θ ^ q) * |F| ^ (rounds + 1) * |domain 0| ^ q`.

There are `|F| ^ (rounds + 1) * |domain 0| ^ q` triples, so this is a fraction
`∑ j, εα j + ∑ i, ε i + θ ^ q` of them: one term for `α`, one for the folding
challenges, one for the queries. -/
theorem pcs_interactive_soundness [Fintype F] [DecidableEq F] (S : LdtInstance F) {s : F}
    (hs : s ≠ 0) {m : ℕ → ℕ} {θ : ℝ} {εα ε : ℕ → ℝ} (claims : ∀ j, Fin (m j) → Claim F)
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (hz : ∀ j ≤ S.rounds, ∀ k, (claims j k).z ∉ (S.domain j).image (s * ·))
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (ε i))
    (c : F → (ℕ → F) → ℕ → F → F) (hcausal : ∀ α, CausalStrategy (c α))
    (hfinal : ∀ α β, IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c α β S.rounds))
    (hfail : ∃ j ≤ S.rounds,
      ¬ ClaimsHold ((S.domain j).image (s * ·)) (S.degree j) θ (claims j)) (q : ℕ) :
    ((Finset.univ.filter fun p : F × (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
        QueryAccepts S.rounds (pcsInput s claims p.1) (c p.1 (challengeSeq p.2.1))
          (challengeSeq p.2.1) (p.2.2 t)).card : ℝ) ≤
      (∑ j ∈ Finset.range (S.rounds + 1), εα j + ∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) *
        (Fintype.card F : ℝ) ^ (S.rounds + 1) * ((S.domain 0).card : ℝ) ^ q := by
  have hθ : 0 < θ := PcsDoomed.pos hfail
  have hε : 0 ≤ ∑ i ∈ Finset.range S.rounds, ε i := Finset.sum_nonneg fun i hi =>
    Compose.nonneg_of_stepMCA (hstep i (Finset.mem_range.mp hi))
  obtain ⟨bad, hbad, hgood⟩ := claimsHold_of_pcsInput S hs claims hmca hz
  obtain ⟨j, hj, hjfail⟩ := hfail
  -- `all`: the number of pairs of challenges and query points. `cnt α`: the accepting ones.
  obtain ⟨all, hall⟩ : ∃ all : ℝ,
    all = (Fintype.card F : ℝ) ^ S.rounds * ((S.domain 0).card : ℝ) ^ q := ⟨_, rfl⟩
  have hall0 : 0 ≤ all := by
    rw [hall]
    positivity
  let cnt : F → ℕ := fun α =>
    (Finset.univ.filter fun p : (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
      QueryAccepts S.rounds (pcsInput s claims α) (c α (challengeSeq p.1)) (challengeSeq p.1)
        (p.2 t)).card
  have hsplit : (Finset.univ.filter fun p : F × (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) =>
      ∀ t, QueryAccepts S.rounds (pcsInput s claims p.1) (c p.1 (challengeSeq p.2.1))
        (challengeSeq p.2.1) (p.2.2 t)).card = ∑ α, cnt α := by
    simp only [cnt, Finset.card_filter, Fintype.sum_prod_type]
  -- For each `α`: it is exceptional, or the low-degree test is sound.
  have hpoint : ∀ α, (cnt α : ℝ) ≤ (if α ∈ bad then (1 : ℝ) else 0) * all +
      (∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) * all := by
    intro α
    by_cases hα : α ∈ bad
    · have hle : cnt α ≤ Fintype.card F ^ S.rounds * (S.domain 0).card ^ q := by
        refine (Finset.card_filter_le _ _).trans_eq ?_
        simp [Fintype.card_prod]
      have hle' : (cnt α : ℝ) ≤ all := by
        rw [hall]
        exact_mod_cast hle
      rw [ite_eq_left hα, one_mul]
      exact hle'.trans (le_add_of_nonneg_right
        (mul_nonneg (add_nonneg hε (pow_nonneg hθ.le q)) hall0))
    · rw [ite_eq_right hα, zero_mul, zero_add, hall, ← mul_assoc]
      exact interactive_soundness S (pcsInput s claims α) (c α) (hcausal α) (hfinal α)
        (fun i hi => hstep i hi _) ⟨j, hj, fun hclose => hjfail (hgood α hα j hj hclose)⟩ q
  calc ((Finset.univ.filter fun p : F × (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
        QueryAccepts S.rounds (pcsInput s claims p.1) (c p.1 (challengeSeq p.2.1))
          (challengeSeq p.2.1) (p.2.2 t)).card : ℝ)
      = ∑ α, (cnt α : ℝ) := by rw [hsplit, Nat.cast_sum]
    _ ≤ ∑ α : F, ((if α ∈ bad then (1 : ℝ) else 0) * all +
          (∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) * all) :=
        Finset.sum_le_sum fun α _ => hpoint α
    _ = bad.card * all +
          Fintype.card F * ((∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) * all) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_boole, Finset.filter_univ_mem,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (∑ j ∈ Finset.range (S.rounds + 1), εα j) * Fintype.card F * all +
          Fintype.card F * ((∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) * all) := by
        gcongr
    _ = (∑ j ∈ Finset.range (S.rounds + 1), εα j + ∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) *
          (Fintype.card F : ℝ) ^ (S.rounds + 1) * ((S.domain 0).card : ℝ) ^ q := by
        rw [hall, pow_succ]
        ring

end CertiFri
