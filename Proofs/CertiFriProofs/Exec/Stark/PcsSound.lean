import CertiFriProofs.Exec.Stark.State
import CertiFriProofs.Exec.SoundnessUnconditional

/-!
# The opening protocol of every supported shard is round-by-round sound

The soundness theorems of the STARK take as a hypothesis (`hpcs`) that the
opening protocol is round-by-round sound, with one bound on its errors, for the
shape of every supported shard. This file proves it at the unique-decoding
radius: for agreement `1 - δ` with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`.

## Contents

* `valueBound sys d`: a bound on the number of opened values of a proof.
* `pcsErr sys d δ`: the bound on the errors. With `n = maxLogDegree + logBlowup`,
  the log of the largest domain a supported shard commits on, and
  `c = 2 ^ n * (δ * 2 ^ n + 1) + 1`, it is the largest of
  `valueBound * c / |K|` (batching), `2 * c / |K| / 2 ^ commitPowBits`
  (folding) and `(1 - δ) ^ numQueries / 2 ^ queryPowBits` (queries).
* `pcsErr_nonneg`.
* `rbrSound_pcs_ud`: the opening protocol of a supported shard whose header
  has one activation bit per circuit is round-by-round sound with every error
  at most `pcsErr`.

## How the proof goes

For a shard with a committed matrix, `Supported` gives that no column is
shorter than the final height, so the parameters are Plonky3's
(`n = rounds + logBlowup + logFinalPolyLen`), and the proximity hypotheses hold
at the unique-decoding radius (`curveCA_udThreshold`,
`Compiled.Params.curveMCA_of_rate_of_curveCA`,
`Compiled.Params.stepMCA_of_rate_of_curveCA`); `PcsRbr.rbrSound_grind` then
gives the errors of the rounds, each at most `pcsErr`. The batching error
counts the claims of the shape: for every matrix, its width at each of its
opening points (`length_claimRefs`), which for the shape of a shard is at most
`valueBound` (`length_claimRefs_starkShape_le`). A shard with no committed
matrix has no claim: its claims never fail, every transcript is doomed, and
there is nothing to prove.

## Assumptions

None beyond those in the statement. The errors use the size `2 ^ n` of the
largest domain a supported shard commits on at every level, and are quadratic
in it.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D]

/-- A bound on the number of opened values of a proof, for an extension of
degree `d`: two rows of the main, the lookup and the fixed trace and one row of
quotient chunks, for every circuit. -/
def valueBound (sys : System F D) (d : ℕ) : ℕ :=
  (sys.circuits.toList.map fun c =>
    2 * c.mainWidth + 2 * c.stage2Width + c.quotientDegree * d + 2 * c.preprocessedWidth).sum

/-- **The bound on the errors of the opening protocol**, at agreement `1 - δ`. -/
noncomputable def pcsErr [Fintype K] (sys : System F D) (d : ℕ) (δ : ℝ) : ℝ :=
  max (valueBound sys d *
      ((2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup)
        * (δ * 2 ^ (sys.maxLogDegree + sys.fri.logBlowup) + 1) + 1) / Fintype.card K)
    (max (2 * ((2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup)
        * (δ * 2 ^ (sys.maxLogDegree + sys.fri.logBlowup) + 1) + 1) / Fintype.card K
        / 2 ^ sys.fri.commitPowBits)
      ((1 - δ) ^ sys.fri.numQueries / 2 ^ sys.fri.queryPowBits))

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq K] [Inhabited D]
  [DecidableEq D] in
/-- The bound on the errors is not negative. -/
theorem pcsErr_nonneg [Fintype K] (sys : System F D) (d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ pcsErr (K := K) sys d δ := by
  refine le_max_of_le_left ?_
  positivity

/-! ## The number of claims of a shape -/

/-- The length of a `flatMap` over indexed elements, when the length of a block
does not depend on the index. -/
private theorem length_flatMap_zipIdx {α β : Type} (g : α × ℕ → List β) (s : α → ℕ)
    (h : ∀ x, (g x).length = s x.1) (l : List α) (k : ℕ) :
    ((l.zipIdx k).flatMap g).length = (l.map s).sum := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, h, ih, List.map_cons,
      List.sum_cons]

/-- The sum of a weight over a `flatMap` over indexed elements, when the sum
over a block does not depend on the index. -/
private theorem sum_map_flatMap_zipIdx {α β : Type} (g : α × ℕ → List β) (w : β → ℕ)
    (s : α → ℕ) (h : ∀ x, ((g x).map w).sum = s x.1) (l : List α) (k : ℕ) :
    (((l.zipIdx k).flatMap g).map w).sum = (l.map s).sum := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append, List.sum_append, h, ih,
      List.map_cons, List.sum_cons]

/-- A map over indexed elements that does not read the index. -/
private theorem map_zipIdx_fst {α β : Type} (f : α → β) (l : List α) (k : ℕ) :
    ((l.zipIdx k).map fun p => f p.1) = l.map f := by
  conv_rhs => rw [← List.zipIdx_map_fst k l, List.map_map]
  rfl

/-- The sum of a weight over the values of a partial map is at most the sum of
a bound on the weight of each value. -/
private theorem sum_map_filterMap_le {α β : Type} (f : α → Option β) (w : β → ℕ) (g : α → ℕ)
    (h : ∀ a b, f a = some b → w b ≤ g a) (l : List α) :
    ((l.filterMap f).map w).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases hf : f a with _ | b
    · rw [List.filterMap_cons_none hf]
      exact ih.trans (Nat.le_add_left _ _)
    · rw [List.filterMap_cons_some hf, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a b hf) ih

/-- The widths of the opening points of a shape add up to the width of every
matrix at each of its opening points. -/
private theorem sum_width_pointRefs (lb : ℕ) (shape : ClaimShape) :
    ((pointRefs lb shape).map (·.width)).sum =
      (shape.flatten.map fun m => m.numPoints * m.width).sum := by
  rw [pointRefs, sum_map_flatMap_zipIdx _ _
    (fun mats => (mats.map fun m : MatrixShape => m.numPoints * m.width).sum),
    List.map_flatten, List.sum_flatten, List.map_map]
  · rfl
  · rintro ⟨mats, b⟩
    refine sum_map_flatMap_zipIdx _ _ _ (fun x => ?_) mats 0
    rw [List.map_replicate, List.sum_replicate, smul_eq_mul]

/-- **The number of claims of a shape**: for every matrix, its width at each of
its opening points. -/
private theorem length_claimRefs (lb : ℕ) (shape : ClaimShape) :
    (claimRefs lb shape).length = (shape.flatten.map fun m => m.numPoints * m.width).sum := by
  rw [← sum_width_pointRefs lb shape, claimRefs, List.length_map, List.length_zipIdx]
  refine length_flatMap_zipIdx _ _ (fun x => ?_) _ 0
  rw [List.length_map, List.length_range]

/-- The number of values claimed of the matrices of one commitment to traces:
for every active circuit, the width of its matrix at each opening point. -/
private theorem sum_traceShapes (act : List ℕ) (logDegrees : Array ℕ) (width : ℕ → ℕ) (np : ℕ) :
    ((traceShapes act logDegrees width np).map fun m => m.numPoints * m.width).sum =
      (act.map fun ci => np * width ci).sum := by
  rw [traceShapes, List.map_map]
  exact congrArg List.sum (map_zipIdx_fst (fun ci => np * width ci) act 0)

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- The number of values claimed of the fixed traces: at most two rows of the
fixed trace of every circuit. -/
private theorem sum_fixedShapes_le (sys : System F D) (act : List ℕ) (logDegrees : Array ℕ) :
    ((fixedShapes sys act logDegrees).map fun m => m.numPoints * m.width).sum ≤
      ((List.range sys.circuits.size).map fun ci =>
        2 * (sys.circuits.getD ci default).preprocessedWidth).sum := by
  rw [fixedShapes]
  refine sum_map_filterMap_le _ _ _ (fun ci b hb => ?_) _
  split_ifs at hb
  split at hb
  · cases hb
    exact Nat.le_refl _
  · cases hb
    exact Nat.mul_le_mul_right _ (Nat.le_succ 1)

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- The circuits of a system, by position. -/
private theorem toList_circuits (sys : System F D) :
    sys.circuits.toList =
      (List.range sys.circuits.size).map fun ci => sys.circuits.getD ci default := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < sys.circuits.size := by simpa using h1
  rw [List.getElem_map, List.getElem_range, Array.getElem_toList, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hi, Option.getD_some]

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- **The number of claims of a proof** whose activation bitmap is no longer
than the system is at most `valueBound`: the active circuits are distinct
circuits of the system, each with two rows of its main and of its lookup trace
and one row of quotient chunks, and every circuit has at most two rows of its
fixed trace. -/
private theorem length_claimRefs_starkShape_le (sys : System F D) (d : ℕ) {active : Array Bool}
    (hact : active.size ≤ sys.circuits.size) (logDegrees : Array ℕ) :
    (claimRefs sys.fri.logBlowup (starkShape sys d active logDegrees)).length ≤
      valueBound sys d := by
  have hsub : ∀ f : ℕ → ℕ, ((activeIndices active).map f).sum ≤
      ((List.range sys.circuits.size).map f).sum := fun f =>
    ((List.filter_sublist.trans (List.range_sublist.mpr hact)).map f).sum_le_sum
      fun _ _ => Nat.zero_le _
  have hfixed : (((match sys.preprocessedCommit with
        | some _ => [fixedShapes sys (activeIndices active) logDegrees]
        | none => []).flatten).map fun m : MatrixShape => m.numPoints * m.width).sum ≤
      ((List.range sys.circuits.size).map fun ci =>
        2 * (sys.circuits.getD ci default).preprocessedWidth).sum := by
    split
    · rw [List.flatten_singleton]
      exact sum_fixedShapes_le sys _ _
    · exact Nat.zero_le _
  rw [length_claimRefs, starkShape, List.flatten_append, List.map_append, List.sum_append,
    List.flatten_cons, List.flatten_cons, List.flatten_singleton, List.map_append, List.map_append,
    List.sum_append, List.sum_append, sum_traceShapes, sum_traceShapes, sum_traceShapes,
    valueBound, toList_circuits, List.map_map]
  refine (Nat.add_le_add (Nat.add_le_add (hsub _) (Nat.add_le_add (hsub _) (hsub _))) hfixed).trans
    (le_of_eq ?_)
  simp only [Function.comp_def, List.sum_map_add, one_mul]
  omega

/-! ## Round-by-round soundness -/

/-- Claims of which there are none at any level do not fail, at an agreement of
at most one: they all hold on the whole coset of their level. -/
private theorem not_claimsFail_of_forall_eq_zero {S : LdtInstance K} {s : K} {θ : ℝ}
    (hθ : θ ≤ 1) {m : ℕ → ℕ} (hm : ∀ j, m j = 0) (claims : ∀ j, Fin (m j) → Claim K) :
    ¬ ClaimsFail S s θ claims := by
  rintro ⟨j, -, hfail⟩
  refine hfail ⟨_, Finset.Subset.refl _, mul_le_of_le_one_left (Nat.cast_nonneg _) hθ,
    fun k => ?_⟩
  exact absurd (lt_of_lt_of_eq k.isLt (hm j)) (Nat.not_lt_zero _)

omit [Inhabited D] [DecidableEq D] in
/-- **The opening protocol of a supported shard is round-by-round sound**, at
the unique-decoding radius, with every error at most `pcsErr`. -/
theorem rbrSound_pcs_ud [Fintype K] (M : StarkModel F EF K) (sys : System F D) {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1) (v : ShardView F EF D K)
    (hactive : v.hdr.active.size = sys.circuits.size) (hs : Supported M sys (1 - δ) v) :
    RbrSound (hs.params.rounds + 2)
      (grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomed hs.params.ldt hs.params.shift (1 - δ) hs.params.queries
          (m := hs.params.numClaims)))
      fun _ => pcsErr (K := K) sys M.extData.d δ := by
  rcases hfl : (v.shape M sys).flatten with _ | ⟨m, l⟩
  · -- No committed matrix: there is no claim, and every transcript is doomed.
    have hnil : claimRefs sys.fri.logBlowup (v.shape M sys) = [] := by
      rw [← List.length_eq_zero_iff, length_claimRefs, hfl]
      rfl
    have hzero : ∀ j, hs.params.numClaims j = 0 := fun j => by
      show (levelClaims sys.fri.logBlowup (v.shape M sys) _ j).length = 0
      rw [levelClaims, hnil]
      rfl
    intro i hi t msg hd
    exact (FractionLE.false.mono_right (pcsErr_nonneg sys M.extData.d hδ)).mono_left
      fun c hc => hc fun _ => doomed_of_not_claimsFail
        (not_claimsFail_of_forall_eq_zero (sub_le_self 1 hδ) hzero _)
  · -- Some committed matrix: the parameters are Plonky3's.
    have hm : m ∈ (v.shape M sys).flatten := by
      rw [hfl]
      exact List.mem_cons_self
    have hθ : (0 : ℝ) ≤ 1 - δ := by
      have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) sys.fri.logBlowup
      linarith
    have hheight : sys.fri.logBlowup + sys.fri.logFinalPolyLen ≤
        logMaxHeight sys.fri.logBlowup (v.shape M sys) :=
      (hs.final m hm).trans (le_logMaxHeight hm)
    have hn : hs.params.n = hs.params.rounds + sys.fri.logBlowup + sys.fri.logFinalPolyLen := by
      show logMaxHeight sys.fri.logBlowup (v.shape M sys) =
        logMaxHeight sys.fri.logBlowup (v.shape M sys) -
          (sys.fri.logBlowup + sys.fri.logFinalPolyLen) + sys.fri.logBlowup +
            sys.fri.logFinalPolyLen
      omega
    have hfinal : hs.params.finalDegree = 2 ^ sys.fri.logFinalPolyLen := rfl
    have hca := curveCA_udThreshold K
    -- The errors of the rounds, with the size of the first domain of the shard.
    have h := rbrSound_grind hs.params.ldt hs.params.shift_ne hθ hs.params.queries
      (fun j hj => hs.params.curveMCA_of_rate_of_curveCA hca hn hfinal hδ hrate hj
        (hs.params.numClaims j))
      (fun i hi => hs.params.stepMCA_of_rate_of_curveCA hca hn hfinal hδ hrate hi)
      (powBits sys.fri (v.shape M sys))
    -- The first domain is no larger than the largest the system supports.
    have hc : (2 : ℝ) ^ hs.params.n * (δ * 2 ^ hs.params.n + 1) + 1 ≤
        (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup) *
          (δ * 2 ^ (sys.maxLogDegree + sys.fri.logBlowup) + 1) + 1 := by
      have htwo : hs.params.n ≤ sys.maxLogDegree + sys.fri.logBlowup := hs.height
      gcongr <;> norm_num
    have h2n_ge : (1 : ℝ) ≤ (2 : ℝ) ^ hs.params.n := one_le_pow₀ (by norm_num)
    have hlin_le : (1 + δ) * (2 : ℝ) ^ hs.params.n ≤
        (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup) *
          (δ * 2 ^ (sys.maxLogDegree + sys.fri.logBlowup) + 1) + 1 := by
      set X : ℝ := (2 : ℝ) ^ hs.params.n
      have h1 : (1 + δ) * X ≤ X * (δ * X + 1) + 1 := by
        have hX : 0 ≤ X * (X - 1) := mul_nonneg (by linarith) (by linarith)
        have hdX : 0 ≤ δ * (X * (X - 1)) := mul_nonneg hδ hX
        linarith
      exact h1.trans hc
    have h1d_le : 1 + δ ≤ 2 := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ sys.fri.logBlowup := pow_nonneg (by norm_num) _
      linarith
    have h2n_le : (2 : ℝ) ^ hs.params.n ≤
        (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup) *
          (δ * 2 ^ (sys.maxLogDegree + sys.fri.logBlowup) + 1) + 1 := by
      set X : ℝ := (2 : ℝ) ^ hs.params.n
      have h1 : X ≤ X * (δ * X + 1) + 1 := by
        have hdX2 : 0 ≤ δ * (X * X) := mul_nonneg hδ (mul_nonneg (by linarith) (by linarith))
        linarith
      exact h1.trans hc
    intro i hi t msg hd
    refine (h i hi t msg hd).mono_right ?_
    beta_reduce
    rcases i with _ | k
    · -- The batching round.
      rw [powBits_zero, pow_zero, div_one, roundError_zero, ← Finset.sum_div, ← Finset.sum_mul]
      have hsum : (∑ j ∈ Finset.range (hs.params.ldt.rounds + 1),
          ((hs.params.numClaims j - 1 : ℕ) : ℝ)) ≤ (valueBound sys M.extData.d : ℝ) := by
        exact_mod_cast (sum_numClaims_sub_one_le M.toFieldModel sys.fri (v.shape M sys)
          (M.wellFormed sys.fri _ hs.two)).trans
            (length_claimRefs_starkShape_le sys M.extData.d hactive.le v.hdr.logDegrees)
      refine le_trans ?_ (le_max_left _ _)
      gcongr
    · rcases Nat.lt_or_ge k hs.params.ldt.rounds with hk | hk
      · -- A folding round.
        rw [powBits_succ_of_lt sys.fri (v.shape M sys) hk, roundError_succ_of_lt hk]
        refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
        gcongr
      · -- The query round.
        obtain rfl : k = numRounds sys.fri (v.shape M sys) := by
          have hR : hs.params.ldt.rounds = numRounds sys.fri (v.shape M sys) := rfl
          have hR' : hs.params.rounds = numRounds sys.fri (v.shape M sys) := rfl
          omega
        rw [powBits_last, roundError_succ_of_not_lt (Nat.not_lt.mpr hk)]
        exact (le_max_right _ _).trans (le_max_right _ _)

end CertiFri.Exec.Stark
