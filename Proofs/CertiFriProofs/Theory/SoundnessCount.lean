import CertiFriProofs.Theory.Soundness
import Mathlib.Data.Fintype.BigOperators

/-!
# Soundness of the low-degree test: counting

Consequences of `query_soundness` in the oracle model, as bounds on the number
of accepting choices of the verifier's randomness.

* `card_accepting_lt`: if some input is far from its code and every folding
  challenge is good, fewer than a fraction `θ` of the query points accept.
  `card_accepting_queries_le` is the same for `q` independent queries.
* `interactive_soundness`: against a prover that chooses each codeword after
  seeing the earlier challenges, the number of pairs of a challenge tuple and a
  query tuple that make the verifier accept is at most
  `(∑ i, ε i + θ ^ q) * |F| ^ rounds * |domain 0| ^ q`.
* The same two facts round by round, for a Fiat–Shamir analysis:
  `LdtInstance.Doomed` is the state "some input is far and every challenge so
  far was good"; `LdtInstance.Doomed.card_escape_le` bounds the challenges that
  leave it, and `LdtInstance.Doomed.card_accepting_queries_le` bounds the
  accepting queries in it.

What is assumed: the proximity hypothesis `StepMCAFor` for each round, and that
the final message is a codeword (in the protocol it is a polynomial sent in the
clear). The bounds are counts; no probability space is set up. Nothing here is
about Merkle trees, random oracles, or the distance of Reed–Solomon codes.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Queries -/

namespace Soundness

/-- Every function is `θ`-close to the code when `θ * |D| ≤ 0`: the empty set is
a large enough agreement set. -/
theorem closeToCode_of_nonpos {D : Finset F} {d : ℕ} {θ : ℝ} (f : F → F)
    (h : θ * D.card ≤ 0) : CloseToCode D d θ f :=
  ⟨0, by rw [degree_zero]; exact WithBot.bot_lt_coe d, ∅, Finset.empty_subset D,
    by simpa using h, fun x hx => absurd hx (Finset.notMem_empty x)⟩

/-- If some input is far from its code, `θ` is positive. -/
theorem pos_of_far (S : LdtInstance F) {θ : ℝ} {ro : ℕ → F → F}
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) : 0 < θ := by
  obtain ⟨i, _, hi⟩ := hfar
  by_contra hθ
  exact hi (closeToCode_of_nonpos _
    (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hθ) (Nat.cast_nonneg _)))

/-- The number of `q`-tuples of points of `D` that all satisfy `Q` is the
`q`-th power of the number of points of `D` that satisfy `Q`. -/
theorem card_filter_forall {α : Type*} (D : Finset α) (Q : α → Prop) [DecidablePred Q] (q : ℕ) :
    (Finset.univ.filter fun xs : Fin q → ↥D => ∀ t, Q (xs t)).card = (D.filter Q).card ^ q := by
  have hpi : (Finset.univ.filter fun xs : Fin q → ↥D => ∀ t, Q (xs t)) =
      Fintype.piFinset fun _ : Fin q => Finset.univ.filter fun x : ↥D => Q x := by
    ext xs
    simp [Fintype.mem_piFinset]
  have hone : (Finset.univ.filter fun x : ↥D => Q x).card = (D.filter Q).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext x
    simp [and_comm]
  rw [hpi, Fintype.card_piFinset, Finset.prod_const, hone, Finset.card_univ, Fintype.card_fin]

end Soundness

/-- If the final message is a codeword, every folding challenge is good, and
some input is not `θ`-close to its code, then fewer than a fraction `θ` of the
query points accept. -/
theorem card_accepting_lt (S : LdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    [DecidablePred fun x => QueryAccepts S.rounds ro c β x]
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds, GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ro (i + 1)) (c i) (β i))
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) :
    (((S.domain 0).filter fun x => QueryAccepts S.rounds ro c β x).card : ℝ) <
      θ * (S.domain 0).card := by
  by_contra hlt
  obtain ⟨i, hi, hfar⟩ := hfar
  exact hfar (query_soundness S ro c β hfinal hgood _ (Finset.filter_subset _ _)
    (fun x hx => (Finset.mem_filter.mp hx).2) (not_lt.mp hlt) i hi)

/-- The same for `q` independent queries: the number of `q`-tuples of query
points that all accept is at most `(θ * |domain 0|) ^ q`. -/
theorem card_accepting_queries_le (S : LdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    [DecidablePred fun x => QueryAccepts S.rounds ro c β x]
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds, GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ro (i + 1)) (c i) (β i))
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) (q : ℕ) :
    ((Finset.univ.filter fun xs : Fin q → ↥(S.domain 0) =>
        ∀ t, QueryAccepts S.rounds ro c β (xs t)).card : ℝ) ≤ (θ * (S.domain 0).card) ^ q := by
  rw [Soundness.card_filter_forall, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_accepting_lt S ro c β hfinal hgood hfar).le q

/-! ## Challenges -/

section Challenges

variable [Fintype F]

open Classical in
/-- `StepMCAFor` as a count: whatever `c` the prover committed to, at most
`ε * |F|` challenges are not good. -/
theorem StepMCAFor.card_bad_le {D D' : Finset F} {d' : ℕ} {θ ε : ℝ} {ro : F → F}
    (h : StepMCAFor D D' d' θ ε ro) (c : F → F) :
    ((Finset.univ.filter fun β : F => ¬ GoodChallenge D D' d' θ ro c β).card : ℝ) ≤
      ε * Fintype.card F := by
  obtain ⟨bad, hcard, hbad⟩ := h c
  refine le_trans ?_ hcard
  exact_mod_cast Finset.card_le_card fun β hβ => by
    by_contra hmem
    exact (Finset.mem_filter.mp hβ).2 (hbad β hmem)

namespace Soundness

open Classical in
/-- Counting in a product. Let `bad β` be a set of values that does not depend
on coordinate `i` of `β` and has at most `K * |F|` elements. Then at most
`K * |F| ^ |ι|` tuples `β` have their coordinate `i` in `bad β`. -/
theorem card_filter_coord_mem_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (bad : (ι → F) → Finset F) {K : ℝ}
    (hbad : ∀ (β : ι → F) (a : F), bad (Function.update β i a) = bad β)
    (hK : ∀ β, ((bad β).card : ℝ) ≤ K * Fintype.card F) :
    ((Finset.univ.filter fun β : ι → F => β i ∈ bad β).card : ℝ) ≤
      K * (Fintype.card F : ℝ) ^ Fintype.card ι := by
  -- Swapping coordinate `i` with an extra value is an involution of `(ι → F) × F`.
  let σ : (ι → F) × F → (ι → F) × F := fun p => (Function.update p.1 i p.2, p.1 i)
  have hσ : Function.Involutive σ := fun p => by simp [σ]
  have key : Fintype.card F * (Finset.univ.filter fun β : ι → F => β i ∈ bad β).card =
      ∑ β : ι → F, (bad β).card := by
    calc Fintype.card F * (Finset.univ.filter fun β : ι → F => β i ∈ bad β).card
        = ∑ p : (ι → F) × F, if p.1 i ∈ bad p.1 then 1 else 0 := by
          rw [Fintype.sum_prod_type, Finset.card_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => ?_
          by_cases h : β i ∈ bad β <;> simp [h]
      _ = ∑ p : (ι → F) × F, if (σ p).1 i ∈ bad (σ p).1 then 1 else 0 :=
          (hσ.bijective.sum_comp fun p => if p.1 i ∈ bad p.1 then 1 else 0).symm
      _ = ∑ p : (ι → F) × F, if p.2 ∈ bad p.1 then 1 else 0 := by simp [σ, hbad]
      _ = ∑ β : ι → F, (bad β).card := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun β _ => ?_
          simp only [Finset.sum_boole, Finset.filter_univ_mem, Nat.cast_id]
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine le_of_mul_le_mul_left ?_ hF
  calc (Fintype.card F : ℝ) * (Finset.univ.filter fun β : ι → F => β i ∈ bad β).card
      = ∑ β : ι → F, ((bad β).card : ℝ) := by exact_mod_cast key
    _ ≤ ∑ _β : ι → F, K * Fintype.card F := Finset.sum_le_sum fun β _ => hK β
    _ = Fintype.card F * (K * (Fintype.card F : ℝ) ^ Fintype.card ι) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
      push_cast
      ring

end Soundness

end Challenges

/-! ## An adaptive prover -/

/-- A tuple of `r` challenges as a sequence indexed by `ℕ`, with zeros from
position `r` on. -/
def challengeSeq {r : ℕ} (β : Fin r → F) (i : ℕ) : F :=
  if h : i < r then β ⟨i, h⟩ else 0

/-- Below `r`, the sequence of a challenge tuple is the tuple. -/
theorem challengeSeq_of_lt {r : ℕ} (β : Fin r → F) {i : ℕ} (h : i < r) :
    challengeSeq β i = β ⟨i, h⟩ :=
  dite_eq_left h

/-- A prover strategy gives the committed codewords as a function of the
challenges. It is causal when the codeword of level `i` depends only on the
challenges before round `i`. -/
def CausalStrategy (c : (ℕ → F) → ℕ → F → F) : Prop :=
  ∀ β β' : ℕ → F, ∀ i, (∀ j < i, β j = β' j) → c β i = c β' i

section Adaptive

variable [Fintype F]

namespace Soundness

open Classical in
/-- Against a causal strategy, at most `ε * |F| ^ r` of the challenge tuples
have a challenge of round `i` that is not good. -/
theorem card_bad_round_le {r : ℕ} {D D' : Finset F} {d' : ℕ} {θ ε : ℝ} {ro : F → F}
    (hmca : StepMCAFor D D' d' θ ε ro) {c : (ℕ → F) → ℕ → F → F} (hcausal : CausalStrategy c)
    {i : ℕ} (hi : i < r) :
    ((Finset.univ.filter fun β : Fin r → F =>
        ¬ GoodChallenge D D' d' θ ro (c (challengeSeq β) i) (challengeSeq β i)).card : ℝ) ≤
      ε * (Fintype.card F : ℝ) ^ r := by
  have hbad : ∀ (β : Fin r → F) (a : F),
      c (challengeSeq (Function.update β ⟨i, hi⟩ a)) i = c (challengeSeq β) i := fun β a =>
    hcausal _ _ i fun j hj => by
      have hjr : j < r := hj.trans hi
      rw [challengeSeq_of_lt _ hjr, challengeSeq_of_lt _ hjr, Function.update_of_ne]
      exact fun h => hj.ne (congrArg Fin.val h)
  have h := card_filter_coord_mem_le (⟨i, hi⟩ : Fin r)
    (fun β => Finset.univ.filter fun b : F =>
      ¬ GoodChallenge D D' d' θ ro (c (challengeSeq β) i) b)
    (fun β a => by simp only [hbad]) (fun β => hmca.card_bad_le _)
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, challengeSeq_of_lt _ hi,
    Fintype.card_fin] using h

end Soundness

open Classical in
/-- Soundness against an adaptive prover, as a count. The prover's codewords are
a causal function of the challenges and its final message is always a codeword;
each round satisfies the proximity hypothesis with error `ε i`; some input is
not `θ`-close to its code. Then, among all pairs of `rounds` challenges and `q`
query points, the number that make every query accept is at most
`(∑ i, ε i + θ ^ q) * |F| ^ rounds * |domain 0| ^ q`. There are
`|F| ^ rounds * |domain 0| ^ q` pairs, so this is a fraction `∑ i, ε i + θ ^ q`
of them: one term for a bad challenge in each round, one for the queries. -/
theorem interactive_soundness (S : LdtInstance F) {θ : ℝ} {ε : ℕ → ℝ} (ro : ℕ → F → F)
    (c : (ℕ → F) → ℕ → F → F) (hcausal : CausalStrategy c)
    (hfinal : ∀ β, IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c β S.rounds))
    (hmca : ∀ i < S.rounds, StepMCAFor (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ε i) (ro (i + 1)))
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) (q : ℕ) :
    ((Finset.univ.filter fun p : (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
        QueryAccepts S.rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card : ℝ) ≤
      (∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) * (Fintype.card F : ℝ) ^ S.rounds *
        ((S.domain 0).card : ℝ) ^ q := by
  have hn : (0 : ℝ) ≤ (S.domain 0).card := Nat.cast_nonneg _
  have hθ : 0 < θ := Soundness.pos_of_far S hfar
  -- `Bad β i`: the challenge of round `i` is not good. `cnt β`: the accepting query tuples.
  let Bad : (Fin S.rounds → F) → ℕ → Prop := fun β i =>
    ¬ GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (ro (i + 1))
      (c (challengeSeq β) i) (challengeSeq β i)
  let cnt : (Fin S.rounds → F) → ℕ := fun β =>
    (Finset.univ.filter fun xs : Fin q → ↥(S.domain 0) =>
      ∀ t, QueryAccepts S.rounds ro (c (challengeSeq β)) (challengeSeq β) (xs t)).card
  have hsplit : (Finset.univ.filter fun p : (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) =>
      ∀ t, QueryAccepts S.rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card =
      ∑ β, cnt β := by
    simp only [cnt, Finset.card_filter, Fintype.sum_prod_type]
  -- For each challenge tuple: a bad round, or few accepting queries.
  have hpoint : ∀ β, (cnt β : ℝ) ≤
      (∑ i ∈ Finset.range S.rounds, if Bad β i then (1 : ℝ) else 0) *
        ((S.domain 0).card : ℝ) ^ q + (θ * (S.domain 0).card) ^ q := by
    intro β
    have hterm : ∀ i ∈ Finset.range S.rounds, (0 : ℝ) ≤ if Bad β i then (1 : ℝ) else 0 :=
      fun i _ => by split_ifs <;> norm_num
    by_cases hbad : ∃ i < S.rounds, Bad β i
    · obtain ⟨i, hi, hbad⟩ := hbad
      have hone : (1 : ℝ) ≤ ∑ i ∈ Finset.range S.rounds, if Bad β i then (1 : ℝ) else 0 :=
        calc (1 : ℝ) = if Bad β i then (1 : ℝ) else 0 := (ite_eq_left hbad).symm
          _ ≤ _ := Finset.single_le_sum hterm (Finset.mem_range.mpr hi)
      have hall : (cnt β : ℝ) ≤ ((S.domain 0).card : ℝ) ^ q := by
        have : cnt β ≤ (S.domain 0).card ^ q := by
          refine (Finset.card_filter_le _ _).trans_eq ?_
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
        exact_mod_cast this
      calc (cnt β : ℝ) ≤ 1 * ((S.domain 0).card : ℝ) ^ q := by rwa [one_mul]
        _ ≤ (∑ i ∈ Finset.range S.rounds, if Bad β i then (1 : ℝ) else 0) *
            ((S.domain 0).card : ℝ) ^ q := mul_le_mul_of_nonneg_right hone (pow_nonneg hn q)
        _ ≤ _ := le_add_of_nonneg_right (pow_nonneg (mul_nonneg hθ.le hn) q)
    · exact (card_accepting_queries_le S ro (c (challengeSeq β)) (challengeSeq β) (hfinal _)
        (fun i hi => not_not.mp fun h => hbad ⟨i, hi, h⟩) hfar q).trans
        (le_add_of_nonneg_left (mul_nonneg (Finset.sum_nonneg hterm) (pow_nonneg hn q)))
  -- For each round: few challenge tuples are bad.
  have hround : ∀ i ∈ Finset.range S.rounds,
      (∑ β : Fin S.rounds → F, if Bad β i then (1 : ℝ) else 0) ≤
        ε i * (Fintype.card F : ℝ) ^ S.rounds := by
    intro i hi
    rw [Finset.sum_boole]
    exact Soundness.card_bad_round_le (hmca i (Finset.mem_range.mp hi)) hcausal
      (Finset.mem_range.mp hi)
  calc ((Finset.univ.filter fun p : (Fin S.rounds → F) × (Fin q → ↥(S.domain 0)) => ∀ t,
        QueryAccepts S.rounds ro (c (challengeSeq p.1)) (challengeSeq p.1) (p.2 t)).card : ℝ)
      = ∑ β, (cnt β : ℝ) := by rw [hsplit, Nat.cast_sum]
    _ ≤ ∑ β : Fin S.rounds → F,
          ((∑ i ∈ Finset.range S.rounds, if Bad β i then (1 : ℝ) else 0) *
            ((S.domain 0).card : ℝ) ^ q + (θ * (S.domain 0).card) ^ q) :=
        Finset.sum_le_sum fun β _ => hpoint β
    _ = (∑ i ∈ Finset.range S.rounds, ∑ β : Fin S.rounds → F, if Bad β i then (1 : ℝ) else 0) *
          ((S.domain 0).card : ℝ) ^ q +
          (Fintype.card F : ℝ) ^ S.rounds * (θ * (S.domain 0).card) ^ q := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm, Finset.sum_const,
          Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ (∑ i ∈ Finset.range S.rounds, ε i * (Fintype.card F : ℝ) ^ S.rounds) *
          ((S.domain 0).card : ℝ) ^ q +
          (Fintype.card F : ℝ) ^ S.rounds * (θ * (S.domain 0).card) ^ q :=
        add_le_add_left
          (mul_le_mul_of_nonneg_right (Finset.sum_le_sum hround) (pow_nonneg hn q)) _
    _ = (∑ i ∈ Finset.range S.rounds, ε i + θ ^ q) * (Fintype.card F : ℝ) ^ S.rounds *
          ((S.domain 0).card : ℝ) ^ q := by
        rw [← Finset.sum_mul, mul_pow]
        ring

end Adaptive

/-! ## Round by round

The two facts behind `interactive_soundness`, stated for one transcript: `c i`
and `β i` for `i < k` are the codewords and challenges of the first `k` rounds.
A Fiat–Shamir analysis uses them with `Doomed` as the state function. -/

/-- The doomed state after `k` rounds: some input is not `θ`-close to its code,
and each of the first `k` challenges was good. It depends on `c i` and `β i`
only for `i < k`. -/
def LdtInstance.Doomed (S : LdtInstance F) (θ : ℝ) (ro c : ℕ → F → F) (β : ℕ → F) (k : ℕ) :
    Prop :=
  (∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) ∧
    ∀ i < k, GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ro (i + 1)) (c i) (β i)

/-- Before the first round, the state is doomed exactly when some input is far. -/
theorem LdtInstance.doomed_zero_iff (S : LdtInstance F) (θ : ℝ) (ro c : ℕ → F → F)
    (β : ℕ → F) :
    S.Doomed θ ro c β 0 ↔ ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i) :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩⟩

/-- The state stays doomed through round `k` exactly when challenge `k` is good. -/
theorem LdtInstance.doomed_succ_iff (S : LdtInstance F) (θ : ℝ) (ro c : ℕ → F → F)
    (β : ℕ → F) (k : ℕ) :
    S.Doomed θ ro c β (k + 1) ↔ S.Doomed θ ro c β k ∧
      GoodChallenge (S.domain k) (S.domain (k + 1)) (S.degree (k + 1)) θ (ro (k + 1)) (c k)
        (β k) := by
  refine ⟨fun h => ⟨⟨h.1, fun i hi => h.2 i (Nat.lt_succ_of_lt hi)⟩, h.2 k (Nat.lt_succ_self k)⟩,
    fun h => ⟨h.1.1, fun i hi => ?_⟩⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · exact h.1.2 i hlt
  · exact h.2

/-- The doomed state after `k` rounds depends only on the first `k` codewords
and challenges. -/
theorem LdtInstance.Doomed.congr {S : LdtInstance F} {θ : ℝ} {ro c c' : ℕ → F → F}
    {β β' : ℕ → F} {k : ℕ} (h : S.Doomed θ ro c β k) (hc : ∀ i < k, c' i = c i)
    (hβ : ∀ i < k, β' i = β i) : S.Doomed θ ro c' β' k :=
  ⟨h.1, fun i hi => by rw [hc i hi, hβ i hi]; exact h.2 i hi⟩

open Classical in
/-- Round `k` of a doomed transcript. Whatever codeword `c k` the prover
commits to, at most `ε * |F|` values of the next challenge leave the doomed
state. -/
theorem LdtInstance.Doomed.card_escape_le [Fintype F] {S : LdtInstance F} {θ : ℝ}
    {ro c : ℕ → F → F} {β : ℕ → F} {k : ℕ} (h : S.Doomed θ ro c β k) {ε : ℝ}
    (hmca : StepMCAFor (S.domain k) (S.domain (k + 1)) (S.degree (k + 1)) θ ε (ro (k + 1))) :
    ((Finset.univ.filter fun b : F =>
        ¬ S.Doomed θ ro c (Function.update β k b) (k + 1)).card : ℝ) ≤ ε * Fintype.card F := by
  refine le_trans ?_ (hmca.card_bad_le (c k))
  exact_mod_cast Finset.card_le_card fun b hb => by
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨hb.1, fun hgood => hb.2 ((S.doomed_succ_iff θ ro c _ k).mpr ⟨?_, ?_⟩)⟩
    · exact h.congr (fun _ _ => rfl) fun i hi => Function.update_of_ne hi.ne _ _
    · rwa [Function.update_self]

/-- A doomed transcript after the last round, one query: if the final message
is a codeword, fewer than a fraction `θ` of the query points accept. -/
theorem LdtInstance.Doomed.card_accepting_lt {S : LdtInstance F} {θ : ℝ} {ro c : ℕ → F → F}
    {β : ℕ → F} [DecidablePred fun x => QueryAccepts S.rounds ro c β x]
    (h : S.Doomed θ ro c β S.rounds)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds)) :
    (((S.domain 0).filter fun x => QueryAccepts S.rounds ro c β x).card : ℝ) <
      θ * (S.domain 0).card :=
  CertiFri.card_accepting_lt S ro c β hfinal h.2 h.1

/-- A doomed transcript after the last round, `q` queries: if the final message
is a codeword, at most `(θ * |domain 0|) ^ q` of the `q`-tuples of query points
all accept. -/
theorem LdtInstance.Doomed.card_accepting_queries_le {S : LdtInstance F} {θ : ℝ}
    {ro c : ℕ → F → F} {β : ℕ → F} [DecidablePred fun x => QueryAccepts S.rounds ro c β x]
    (h : S.Doomed θ ro c β S.rounds)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds)) (q : ℕ) :
    ((Finset.univ.filter fun xs : Fin q → ↥(S.domain 0) =>
        ∀ t, QueryAccepts S.rounds ro c β (xs t)).card : ℝ) ≤ (θ * (S.domain 0).card) ^ q :=
  CertiFri.card_accepting_queries_le S ro c β hfinal h.2 h.1 q

end CertiFri
