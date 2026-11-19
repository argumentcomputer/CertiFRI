import Mathlib
import CertiFriProofs.Theory.Basic

/-!
# From the low-degree test to evaluation claims

The verifier is a polynomial commitment verifier. A *claim* says that a
committed function `f` is (close to) a polynomial that takes the value `y` at
the point `z`. The verifier does not test claims directly. For each height it
forms the *reduced opening*, the combination with powers of one challenge `α`
of the quotients `(y - f x) / (z - x)`, and runs the low-degree test on that.
This file proves what closeness of the reduced openings to the code implies for
the claims.

## Results

* `exists_poly_of_quotient`: a quotient that agrees with a polynomial of degree
  below `d` on a set forces `f` to agree there with a polynomial of degree at
  most `d` that takes the value `y` at `z`.
* `isCodeword_quotientAt`, `isCodeword_reducedOpening`: completeness. The
  quotient of a true claim, and the reduced opening of true claims, are
  codewords (of degree below `d - 1`, in the `_pred` forms).
  `reducedOpening_eq_zero_of_degree_lt_one` is the case of constants.
* `claims_of_reducedOpening`: for all but an `ε` fraction of `α`, a reduced
  opening that is close to the code makes every claim of that height true of a
  polynomial that its function agrees with on one common dense set.
  `claims_of_reducedOpening_heights` is the same for several heights sharing
  `α`, with the errors added.
* `eq_of_agree_of_unique`, `claims_of_reducedOpening_unique`,
  `claims_of_reducedOpening_heights_unique`: in the unique-decoding regime a
  function is close to at most one polynomial, so all claims about one
  function are about one polynomial, which does not depend on `α`.

## Assumptions

The batched theorems take `CurveMCA` as a hypothesis and do not prove it. They
are implications from `CloseToCode D d θ (reducedOpening α claims)`: that an
accepting low-degree test yields this closeness is not proved here.

## Correspondence with `open_inputs`

`open_inputs` (Plonky3, `fri/src/verifier.rs`) receives the query indices, the
challenge `alpha`, and for every batch (one commitment) its matrices, each with
its domain and a list of pairs `(z, ps_at_z)`: an opening point and the claimed
values at `z` of all columns of the matrix. For one query it keeps a map from
`log_height` to a pair `(alpha_pow, ro)`, created as `(1, 0)` when a height
first occurs. It loops over the batches, inside that over the matrices of the
batch, inside that over the opening points of the matrix, inside that over the
columns of the matrix, and performs on the entry of the height of the matrix
(`log2 (domain size) + log_blowup`)

    ro += alpha_pow * (p_at_z - p_at_x) * (z - x)⁻¹;  alpha_pow *= alpha

where `p_at_x` is the opened value of the column at the query point `x` and
`p_at_z` its claimed value at `z`. The inverses `(z - x)⁻¹` come from a pass
before the loop, which visits the same matrices and opening points in the same
order and inverts all the differences at once. The model reads this as follows.

* A claim `(f, z, y)` is one column at one opening point: `f` is the column as
  a function on the evaluation domain (`p_at_x = f x`), and `y = p_at_z`. A
  matrix opened at several points gives several claims about each column.
* The power counter is per height. The entry of one height after the loop is
  `reducedOpening α claims x`, where `claims` lists the claims of the matrices
  of that height in loop order: batch, then matrix, then opening point, then
  column. Claim number `k` of its height has the weight `α ^ k` whatever claims
  of other heights the loop visits in between. `reducedOpening_zero` and
  `reducedOpening_succ` are the initial value and the step of the loop, and
  `foldl_eq_reducedOpening` is the loop on a list of claims.
* One `alpha`, sampled once in `verify_fri`, serves all heights. This is why
  `claims_of_reducedOpening_heights` has a single exceptional set. The
  exceptional set depends on the claims alone, so the claims must be fixed
  before `α` is drawn; `TwoAdicFriPcs::verify` passes the claimed values to the
  challenger before it calls `verify_fri`.
* The query point is `x = GENERATOR * g ^ rev (index >> bits_reduced)`, with
  `g` the generator of the subgroup of order `2 ^ log_height` and `rev` the
  reversal of `log_height` bits. So the domain `D` of this file is the coset of
  that subgroup by `GENERATOR`, and `f` is a function on the coset. The
  low-degree test runs on the subgroup itself; the transfer between the coset
  and the subgroup is not in this file.
* The pass that computes the inverses rejects the proof when some `z - x` is
  zero (`OpeningPointMatchesQueryPoint`). It sees the queried points only. The
  theorems with the hypothesis `hz` assume more, that no opening point lies in
  `D`. In the model the quotient at `x = z` is zero (division by zero), where
  the verifier rejects, so the verifier is at least as strict as the model.
  Without `hz`, `claims_of_reducedOpening_off_points` gives the conclusion
  away from the opening point of each claim.
* `p_at_x` lies in the base field, and `z`, `p_at_z`, `alpha` in the extension
  field. Here everything lies in one field `F`, the extension field.

## Not modeled

* The check after the loop that the reduced opening at height `log_blowup` is
  zero. That height holds the matrices of height one, whose honest columns are
  constants. `reducedOpening_eq_zero_of_degree_lt_one` says an honest prover
  passes it; nothing is proved about what it adds to soundness.
* The Merkle authentication of the opened values (`verify_multi_batch`) and
  the shape checks on the proof. The value `f x` is read from the function.
* Which point of the coset of each height a query visits (`index >>
  bits_reduced`). That belongs to the model of the query.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Claims and reduced openings -/

/-- One evaluation claim: the function `f` takes the value `y` at `z`. -/
structure Claim (F : Type*) where
  /-- The committed function. Only its values on the evaluation domain matter. -/
  f : F → F
  /-- The opening point. -/
  z : F
  /-- The claimed value at the opening point. -/
  y : F

/-- The quotient Plonky3 forms for one claim at the domain point `x`:
`(p_at_z - p_at_x) * (z - x)⁻¹`. It is zero when `x = z`, a query the verifier
rejects. -/
def quotientAt (f : F → F) (z y x : F) : F := (y - f x) / (z - x)

/-- The reduced opening of the claims of one height at `x`: claim `k` enters
with `α ^ k`. -/
def reducedOpening {m : ℕ} (α : F) (claims : Fin m → Claim F) (x : F) : F :=
  ∑ k : Fin m, α ^ (k : ℕ) * quotientAt (claims k).f (claims k).z (claims k).y x

/-- The quotient in the form the verifier computes it, with the inverse of
`z - x`. -/
theorem quotientAt_eq_mul_inv (f : F → F) (z y x : F) :
    quotientAt f z y x = (y - f x) * (z - x)⁻¹ :=
  div_eq_mul_inv _ _

/-- With no claims the reduced opening is zero: the initial value of the
verifier's loop. -/
@[simp]
theorem reducedOpening_zero (α : F) (claims : Fin 0 → Claim F) (x : F) :
    reducedOpening α claims x = 0 := by
  simp [reducedOpening]

/-- One step of the verifier's loop: after `m` claims, the next claim is added
with the weight `α ^ m`. -/
theorem reducedOpening_succ {m : ℕ} (α : F) (claims : Fin (m + 1) → Claim F) (x : F) :
    reducedOpening α claims x = reducedOpening α (fun k => claims k.castSucc) x +
      α ^ m * quotientAt (claims (Fin.last m)).f (claims (Fin.last m)).z
        (claims (Fin.last m)).y x := by
  simp [reducedOpening, Fin.sum_univ_castSucc]

/-- The loop of `foldl_eq_reducedOpening` from an arbitrary state. -/
private theorem foldl_aux (α x : F) (cs : List (Claim F)) (a r : F) :
    cs.foldl (fun s c => (s.1 * α, s.2 + s.1 * (c.y - c.f x) * (c.z - x)⁻¹)) (a, r) =
      (a * α ^ cs.length, r + a * reducedOpening α cs.get x) := by
  induction cs generalizing a r with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    simp only [reducedOpening, List.length_cons, Fin.sum_univ_succ, quotientAt_eq_mul_inv,
      Finset.mul_sum, mul_add, pow_succ, List.get_eq_getElem, Fin.val_zero, pow_zero, one_mul,
      Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    rw [add_assoc]
    congr 2
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring

/-- The accumulation loop of `open_inputs` on the claims of one height, in loop
order. The state is the pair `(alpha_pow, ro)`, starting at `(1, 0)`; each
claim adds `alpha_pow * (y - f x) * (z - x)⁻¹` to `ro` and multiplies
`alpha_pow` by `α`. The loop ends with `ro` equal to the reduced opening. -/
theorem foldl_eq_reducedOpening (α x : F) (cs : List (Claim F)) :
    cs.foldl (fun s c => (s.1 * α, s.2 + s.1 * (c.y - c.f x) * (c.z - x)⁻¹)) ((1 : F), (0 : F)) =
      (α ^ cs.length, reducedOpening α cs.get x) := by
  simpa using foldl_aux α x cs 1 0

/-! ## One quotient -/

/-- If the quotient agrees with a polynomial of degree below `d` on `B`, the
function agrees on `B` with a polynomial of degree at most `d` that takes the
value `y` at `z`.

The degree bound of the conclusion is one more than an honest polynomial has:
the test bounds the degree of the quotient by `d`, where the quotient of an
honest polynomial has degree below `d - 1`. This is a property of the protocol. -/
theorem exists_poly_of_quotient {f : F → F} {z y : F} {q : F[X]} {d : ℕ} {B : Finset F}
    (hq : q.degree < d) (hz : z ∉ B) (h : ∀ x ∈ B, quotientAt f z y x = q.eval x) :
    ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧ P.eval z = y ∧ ∀ x ∈ B, f x = P.eval x := by
  refine ⟨C y - (C z - X) * q, ?_, by simp, fun x hx => ?_⟩
  · have h1 : (C y : F[X]).degree < (d + 1 : ℕ) :=
      degree_C_le.trans_lt (by exact_mod_cast Nat.succ_pos d)
    have h2 : ((C z - X : F[X]) * q).degree < (d + 1 : ℕ) := by
      have hl : (C z - X : F[X]).degree ≤ 1 :=
        (degree_sub_le _ _).trans (max_le (degree_C_le.trans zero_le_one) degree_X_le)
      calc ((C z - X : F[X]) * q).degree ≤ (C z - X : F[X]).degree + q.degree :=
            degree_mul_le _ _
        _ ≤ 1 + q.degree := by gcongr
        _ < 1 + (d : WithBot ℕ) := WithBot.add_lt_add_left WithBot.one_ne_bot hq
        _ = (d + 1 : ℕ) := by rw [Nat.cast_add, Nat.cast_one, add_comm]
    exact (degree_sub_le _ _).trans_lt (max_lt h1 h2)
  · have hzx : z - x ≠ 0 := sub_ne_zero.mpr fun e => hz (e ▸ hx)
    have hx' := h x hx
    rw [quotientAt, div_eq_iff hzx] at hx'
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    linear_combination -hx'

/-- A codeword of a code is a codeword of every larger code. -/
theorem Quotient.isCodeword_mono {D : Finset F} {d d' : ℕ} {f : F → F} (h : d ≤ d')
    (hf : IsCodeword D d f) : IsCodeword D d' f := by
  obtain ⟨p, hp, hpf⟩ := hf
  exact ⟨p, hp.trans_le (by exact_mod_cast h), hpf⟩

/-- A codeword of the code of dimension zero vanishes on the domain. -/
theorem Quotient.isCodeword_zero_iff {D : Finset F} {f : F → F} :
    IsCodeword D 0 f ↔ ∀ x ∈ D, f x = 0 := by
  constructor
  · rintro ⟨p, hp, h⟩ x hx
    have hp0 : p = 0 := degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hp))
    rw [h x hx, hp0, eval_zero]
  · exact fun h => ⟨0, by simp, fun x hx => by rw [h x hx, eval_zero]⟩

/-- Completeness for one claim, with the sharp degree. If `f` is a polynomial
of degree below `d` on `D` that takes the value `y` at `z`, and `z` is outside
`D`, the quotient is a polynomial of degree below `d - 1` on `D`. -/
theorem isCodeword_quotientAt_pred {D : Finset F} {d : ℕ} {f : F → F} {z y : F} {P : F[X]}
    (hP : P.degree < d) (hy : P.eval z = y) (hz : z ∉ D) (hf : ∀ x ∈ D, f x = P.eval x) :
    IsCodeword D (d - 1) (quotientAt f z y) := by
  have hmul : (X - C z) * ((P - C y) /ₘ (X - C z)) = P - C y :=
    mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot, hy])
  refine ⟨(P - C y) /ₘ (X - C z), ?_, fun x hx => ?_⟩
  · by_cases h0 : P - C y = 0
    · rw [h0, zero_divByMonic, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hd : (P - C y).degree < d := by
        refine (degree_sub_le _ _).trans_lt (max_lt hP (degree_C_le.trans_lt ?_))
        rcases Nat.eq_zero_or_pos d with rfl | hpos
        · have hP0 : P = 0 :=
            degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hP))
          subst hP0
          simp [← hy] at h0
        · exact_mod_cast hpos
      have hlt := degree_divByMonic_lt (P - C y) (X - C z) h0
        (by rw [degree_X_sub_C]; exact zero_lt_one)
      rw [degree_eq_natDegree h0] at hlt
      refine hlt.trans_le ?_
      exact_mod_cast Nat.le_sub_one_of_lt ((natDegree_lt_iff_degree_lt h0).mpr hd)
  · have hzx : z - x ≠ 0 := sub_ne_zero.mpr fun e => hz (e ▸ hx)
    have hev : (x - z) * ((P - C y) /ₘ (X - C z)).eval x = P.eval x - y := by
      simpa using congrArg (eval x) hmul
    rw [quotientAt, hf x hx, div_eq_iff hzx]
    linear_combination hev

/-- Completeness for one claim: the quotient of a true claim is a codeword. -/
theorem isCodeword_quotientAt {D : Finset F} {d : ℕ} {f : F → F} {z y : F} {P : F[X]}
    (hP : P.degree < d) (hy : P.eval z = y) (hz : z ∉ D) (hf : ∀ x ∈ D, f x = P.eval x) :
    IsCodeword D d (quotientAt f z y) :=
  Quotient.isCodeword_mono (Nat.sub_le d 1) (isCodeword_quotientAt_pred hP hy hz hf)

/-- A combination of codewords with powers of `α` is a codeword. -/
theorem Quotient.isCodeword_sum_pow {D : Finset F} {d m : ℕ} (α : F) {u : Fin m → F → F}
    (h : ∀ k, IsCodeword D d (u k)) :
    IsCodeword D d fun x => ∑ k : Fin m, α ^ (k : ℕ) * u k x := by
  choose v hv hu using h
  refine ⟨∑ k : Fin m, α ^ (k : ℕ) • v k, ?_, fun x hx => ?_⟩
  · rw [← mem_degreeLT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_degreeLT.mpr (hv k))
  · simp [eval_finsetSum, hu _ x hx]

/-- Completeness for one height, with the sharp degree. If every claim is true
of a polynomial of degree below `d` that its function equals on `D`, and no
opening point lies in `D`, the reduced opening is a polynomial of degree below
`d - 1` on `D`. -/
theorem isCodeword_reducedOpening_pred {D : Finset F} {d m : ℕ} (α : F)
    {claims : Fin m → Claim F} (hz : ∀ k, (claims k).z ∉ D)
    (h : ∀ k, ∃ P : F[X], P.degree < d ∧ P.eval (claims k).z = (claims k).y ∧
      ∀ x ∈ D, (claims k).f x = P.eval x) :
    IsCodeword D (d - 1) (reducedOpening α claims) :=
  Quotient.isCodeword_sum_pow α fun k =>
    let ⟨_, hP, hy, hf⟩ := h k
    isCodeword_quotientAt_pred hP hy (hz k) hf

/-- Completeness for one height: the reduced opening of true claims is a
codeword. -/
theorem isCodeword_reducedOpening {D : Finset F} {d m : ℕ} (α : F)
    {claims : Fin m → Claim F} (hz : ∀ k, (claims k).z ∉ D)
    (h : ∀ k, ∃ P : F[X], P.degree < d ∧ P.eval (claims k).z = (claims k).y ∧
      ∀ x ∈ D, (claims k).f x = P.eval x) :
    IsCodeword D d (reducedOpening α claims) :=
  Quotient.isCodeword_mono (Nat.sub_le d 1) (isCodeword_reducedOpening_pred α hz h)

/-- The reduced opening of true claims about constants vanishes on `D`. The
verifier checks this at the height of the matrices of height one. -/
theorem reducedOpening_eq_zero_of_degree_lt_one {D : Finset F} {m : ℕ} (α : F)
    {claims : Fin m → Claim F} (hz : ∀ k, (claims k).z ∉ D)
    (h : ∀ k, ∃ P : F[X], P.degree < (1 : ℕ) ∧ P.eval (claims k).z = (claims k).y ∧
      ∀ x ∈ D, (claims k).f x = P.eval x) :
    ∀ x ∈ D, reducedOpening α claims x = 0 :=
  Quotient.isCodeword_zero_iff.mp (isCodeword_reducedOpening_pred α hz h)

/-! ## The batched theorem -/

/-- The batched theorem with no hypothesis on the opening points. For all but
an `ε` fraction of `α`: if the reduced opening is close to the code, there is a
set `B` holding a fraction `θ` of `D` such that every claim is true of a
polynomial of degree at most `d` that its function agrees with on `B`, except
possibly at the opening point of the claim. -/
theorem claims_of_reducedOpening_off_points [Fintype F] {D : Finset F} {d m : ℕ} {θ ε : ℝ}
    (hmca : CurveMCA D d m θ ε) (claims : Fin m → Claim F) :
    ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
      ∀ α ∉ bad, CloseToCode D d θ (reducedOpening α claims) →
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧
          ∀ k, ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧ P.eval (claims k).z = (claims k).y ∧
            ∀ x ∈ B, x ≠ (claims k).z → (claims k).f x = P.eval x := by
  classical
  obtain ⟨bad, hbad, h⟩ := hmca fun k => quotientAt (claims k).f (claims k).z (claims k).y
  refine ⟨bad, hbad, fun α hα ⟨p, hp, B, hBD, hB, hagree⟩ => ?_⟩
  obtain ⟨v, hv, hu⟩ := h α hα p hp B hBD hB hagree
  refine ⟨B, hBD, hB, fun k => ?_⟩
  obtain ⟨P, hP, hPz, hPB⟩ := exists_poly_of_quotient (B := B.erase (claims k).z) (hv k)
    (Finset.notMem_erase _ _) fun x hx => hu k x (Finset.mem_of_mem_erase hx)
  exact ⟨P, hP, hPz, fun x hx hne => hPB x (Finset.mem_erase.mpr ⟨hne, hx⟩)⟩

/-- The batched theorem for one height. For all but an `ε` fraction of `α`: if
the reduced opening is close to the code, there is a set `B` holding a fraction
`θ` of `D` such that every claim is true of a polynomial of degree at most `d`
that its function agrees with on `B`. The set `B` is common to all claims. -/
theorem claims_of_reducedOpening [Fintype F] {D : Finset F} {d m : ℕ} {θ ε : ℝ}
    (hmca : CurveMCA D d m θ ε) (claims : Fin m → Claim F) (hz : ∀ k, (claims k).z ∉ D) :
    ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
      ∀ α ∉ bad, CloseToCode D d θ (reducedOpening α claims) →
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧
          ∀ k, ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧ P.eval (claims k).z = (claims k).y ∧
            ∀ x ∈ B, (claims k).f x = P.eval x := by
  obtain ⟨bad, hbad, h⟩ := claims_of_reducedOpening_off_points hmca claims
  refine ⟨bad, hbad, fun α hα hclose => ?_⟩
  obtain ⟨B, hBD, hB, hk⟩ := h α hα hclose
  refine ⟨B, hBD, hB, fun k => ?_⟩
  obtain ⟨P, hP, hPz, hPB⟩ := hk k
  exact ⟨P, hP, hPz, fun x hx => hPB x hx fun e => hz k (e ▸ hBD hx)⟩

/-- Union bound over the heights: exceptional sets for each height combine
into one whose size is bounded by the sum of the errors. -/
private theorem exists_bad_biUnion [Fintype F] {ι : Type*} (s : Finset ι) (ε : ι → ℝ)
    (Q : ι → F → Prop)
    (h : ∀ j ∈ s, ∃ bad : Finset F, (bad.card : ℝ) ≤ ε j * Fintype.card F ∧ ∀ α ∉ bad, Q j α) :
    ∃ bad : Finset F, (bad.card : ℝ) ≤ (∑ j ∈ s, ε j) * Fintype.card F ∧
      ∀ α ∉ bad, ∀ j ∈ s, Q j α := by
  classical
  choose! bad hcard hQ using h
  refine ⟨s.biUnion bad, ?_, fun α hα j hj =>
    hQ j hj α fun hmem => hα (Finset.mem_biUnion.mpr ⟨j, hj, hmem⟩)⟩
  calc ((s.biUnion bad).card : ℝ) ≤ ((∑ j ∈ s, (bad j).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j ∈ s, ((bad j).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ j ∈ s, ε j * Fintype.card F := Finset.sum_le_sum fun j hj => hcard j hj
    _ = (∑ j ∈ s, ε j) * Fintype.card F := (Finset.sum_mul _ _ _).symm

/-- The batched theorem for several heights sharing one `α`. Height `j` of the
finite family `s` has its domain `D j`, its degree bound `d j` and its
`m j` claims. For all but a `∑ j ∈ s, ε j` fraction of `α`, the conclusion of
`claims_of_reducedOpening` holds at every height of `s`. -/
theorem claims_of_reducedOpening_heights [Fintype F] {ι : Type*} (s : Finset ι)
    {D : ι → Finset F} {d m : ι → ℕ} {θ : ℝ} {ε : ι → ℝ}
    (hmca : ∀ j ∈ s, CurveMCA (D j) (d j) (m j) θ (ε j))
    (claims : ∀ j, Fin (m j) → Claim F) (hz : ∀ j ∈ s, ∀ k, (claims j k).z ∉ D j) :
    ∃ bad : Finset F, (bad.card : ℝ) ≤ (∑ j ∈ s, ε j) * Fintype.card F ∧
      ∀ α ∉ bad, ∀ j ∈ s, CloseToCode (D j) (d j) θ (reducedOpening α (claims j)) →
        ∃ B ⊆ D j, θ * (D j).card ≤ B.card ∧
          ∀ k, ∃ P : F[X], P.degree < (d j + 1 : ℕ) ∧
            P.eval (claims j k).z = (claims j k).y ∧ ∀ x ∈ B, (claims j k).f x = P.eval x :=
  exists_bad_biUnion s ε _ fun j hj => claims_of_reducedOpening (hmca j hj) (claims j) (hz j hj)

/-! ## Unique decoding: one polynomial per committed function -/

/-- Two polynomials of degree below `n` that agree on at least `n` points are
equal. -/
private theorem Quotient.eq_of_degree_lt_of_agree {n : ℕ} {p q : F[X]} {s : Finset F}
    (hp : p.degree < n) (hq : q.degree < n) (hs : n ≤ s.card)
    (h : ∀ x ∈ s, p.eval x = q.eval x) : p = q :=
  eq_of_degrees_lt_of_eval_finset_eq s (hp.trans_le (by exact_mod_cast hs))
    (hq.trans_le (by exact_mod_cast hs)) h

/-- In the unique-decoding regime, two subsets of `D` of density `θ` share more
than `d` points. -/
private theorem Quotient.lt_card_inter {ι : Type*} [DecidableEq ι] {D A B : Finset ι} {d : ℕ}
    {θ : ℝ} (hθ : 2 * (1 - θ) * D.card + d < D.card) (hA : A ⊆ D) (hB : B ⊆ D)
    (hAc : θ * D.card ≤ A.card) (hBc : θ * D.card ≤ B.card) : d < (A ∩ B).card := by
  have h1 : ((A ∩ B).card : ℝ) + (A ∪ B).card = A.card + B.card := by
    exact_mod_cast Finset.card_inter_add_card_union A B
  have h2 : ((A ∪ B).card : ℝ) ≤ D.card := by
    exact_mod_cast Finset.card_le_card (Finset.union_subset hA hB)
  have h3 : (d : ℝ) < (A ∩ B).card := by linarith
  exact_mod_cast h3

/-- Unique decoding. If `2 * (1 - θ) * D.card + d < D.card`, a function agrees
with at most one polynomial of degree at most `d` on a subset of `D` of density
`θ`: two such polynomials are equal, whatever the two subsets. -/
theorem eq_of_agree_of_unique {D : Finset F} {d : ℕ} {θ : ℝ}
    (hθ : 2 * (1 - θ) * D.card + d < D.card) {f : F → F} {P Q : F[X]}
    (hP : P.degree < (d + 1 : ℕ)) (hQ : Q.degree < (d + 1 : ℕ)) {A B : Finset F}
    (hA : A ⊆ D) (hB : B ⊆ D) (hAc : θ * D.card ≤ A.card) (hBc : θ * D.card ≤ B.card)
    (hPA : ∀ x ∈ A, f x = P.eval x) (hQB : ∀ x ∈ B, f x = Q.eval x) : P = Q := by
  classical
  refine Quotient.eq_of_degree_lt_of_agree (s := A ∩ B) hP hQ
    (Quotient.lt_card_inter hθ hA hB hAc hBc) fun x hx => ?_
  rw [← hPA x (Finset.mem_of_mem_inter_left hx), ← hQB x (Finset.mem_of_mem_inter_right hx)]

/-- The batched theorem in the unique-decoding regime. For all but an `ε`
fraction of `α`: if the reduced opening is close to the code, there is a set
`B` holding a fraction `θ` of `D` such that the function of every claim agrees
on `B` with a polynomial `P` of degree at most `d`, every claim about that
function is true of `P`, and `P` is the only polynomial of degree at most `d`
that the function agrees with on a subset of `D` of density `θ`. So `P` depends
on the function alone, not on `α` or on the other claims. -/
theorem claims_of_reducedOpening_unique [Fintype F] {D : Finset F} {d m : ℕ} {θ ε : ℝ}
    (hmca : CurveMCA D d m θ ε) (hθ : 2 * (1 - θ) * D.card + d < D.card)
    (claims : Fin m → Claim F) (hz : ∀ k, (claims k).z ∉ D) :
    ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
      ∀ α ∉ bad, CloseToCode D d θ (reducedOpening α claims) →
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧
          ∀ k, ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
            (∀ x ∈ B, (claims k).f x = P.eval x) ∧
            (∀ k', (claims k').f = (claims k).f → P.eval (claims k').z = (claims k').y) ∧
            ∀ Q : F[X], Q.degree < (d + 1 : ℕ) → ∀ A ⊆ D, θ * D.card ≤ A.card →
              (∀ x ∈ A, (claims k).f x = Q.eval x) → Q = P := by
  obtain ⟨bad, hbad, h⟩ := claims_of_reducedOpening hmca claims hz
  refine ⟨bad, hbad, fun α hα hclose => ?_⟩
  obtain ⟨B, hBD, hB, hk⟩ := h α hα hclose
  choose P hP hPz hPB using hk
  refine ⟨B, hBD, hB, fun k => ⟨P k, hP k, hPB k, fun k' hf => ?_, fun Q hQ A hAD hA hQA => ?_⟩⟩
  · have hPB' : ∀ x ∈ B, (claims k).f x = (P k').eval x := fun x hx => hf ▸ hPB k' x hx
    rw [eq_of_agree_of_unique hθ (hP k) (hP k') hBD hBD hB hB (hPB k) hPB', hPz k']
  · exact eq_of_agree_of_unique hθ hQ (hP k) hAD hBD hA hB hQA (hPB k)

/-- The unique-decoding form of the batched theorem for several heights sharing
one `α`: for all but a `∑ j ∈ s, ε j` fraction of `α`, the conclusion of
`claims_of_reducedOpening_unique` holds at every height of `s`. -/
theorem claims_of_reducedOpening_heights_unique [Fintype F] {ι : Type*} (s : Finset ι)
    {D : ι → Finset F} {d m : ι → ℕ} {θ : ℝ} {ε : ι → ℝ}
    (hmca : ∀ j ∈ s, CurveMCA (D j) (d j) (m j) θ (ε j))
    (hθ : ∀ j ∈ s, 2 * (1 - θ) * (D j).card + d j < (D j).card)
    (claims : ∀ j, Fin (m j) → Claim F) (hz : ∀ j ∈ s, ∀ k, (claims j k).z ∉ D j) :
    ∃ bad : Finset F, (bad.card : ℝ) ≤ (∑ j ∈ s, ε j) * Fintype.card F ∧
      ∀ α ∉ bad, ∀ j ∈ s, CloseToCode (D j) (d j) θ (reducedOpening α (claims j)) →
        ∃ B ⊆ D j, θ * (D j).card ≤ B.card ∧
          ∀ k, ∃ P : F[X], P.degree < (d j + 1 : ℕ) ∧
            (∀ x ∈ B, (claims j k).f x = P.eval x) ∧
            (∀ k', (claims j k').f = (claims j k).f →
              P.eval (claims j k').z = (claims j k').y) ∧
            ∀ Q : F[X], Q.degree < (d j + 1 : ℕ) → ∀ A ⊆ D j, θ * (D j).card ≤ A.card →
              (∀ x ∈ A, (claims j k).f x = Q.eval x) → Q = P :=
  exists_bad_biUnion s ε _ fun j hj =>
    claims_of_reducedOpening_unique (hmca j hj) (hθ j hj) (claims j) (hz j hj)

end CertiFri
