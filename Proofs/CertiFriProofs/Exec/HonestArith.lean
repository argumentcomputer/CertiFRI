import CertiFriProofs.Exec.Honest

/-!
# Completeness: the arithmetic of an honest proof, in the model

For an honest statement (`HonestStatement`) and a query whose opened entries
are the committed ones, this file computes what the model verifier
(`Theory/Compiled/Verifier.lean`) obtains for that query, in terms of the
polynomials of `Exec/Honest.lean`.

* `reduced_eq_eval_inputPoly`: the reduced opening of level `j` is the value of
  `inputPoly` of that level at the query's point of the level.
* `degree_inputPoly_lt`: `inputPoly` of every level respects the degree bound
  of the level.
* `inputPoly_numRounds_eq_zero`: when the final polynomial is a constant,
  `inputPoly` of the last level is zero.
* `folded_eq_eval_honestWord`: if the sibling values of the rounds before `i`
  are the values of the honest words, the fold chain after `i` rounds is the
  value of `honestWord` of level `i` at the query's point of that level.
* `commitRow_eq_eval_honestWord`: under the same hypothesis up to round `i`,
  the row the verifier reconstructs in round `i` holds the values of
  `honestWord` of level `i` at the two points of the row.

## Assumptions

The statement is honest for the committed data `w`. For the three theorems
about a query, the statement and the proof pass `Fri.shapeOk` (of it, only the
number of opening points is used), the query index is below the size of the
first domain, and the opened entries of the query are the entries of the
committed rows at that index. The batching challenge `α` and the folding
challenges `β` are arbitrary.

## Not covered

The Merkle openings, the transcript, the comparison with the final polynomial,
and the executable verifier: everything here is about the values the model
verifier `Compiled.Params` computes for `modelParams`. Nothing is proved about
a prover. The helper lemmas are in the namespace `HonestArith`.
-/

namespace CertiFri.Exec

open Fri Polynomial

namespace HonestArith

/-! ## Rows and degree bounds -/

/-- The row of a value at the index `a` and the value at the other index of
its pair, placed by the low bit of `a`: the values at the indices `2 * (a / 2)`
and `2 * (a / 2) + 1`. -/
theorem placeRow_eq {K : Type} (f : ℕ → K) (a : ℕ) :
    Compiled.placeRow (f a) (f (a ^^^ 1)) a = (f (2 * (a / 2)), f (2 * (a / 2) + 1)) := by
  unfold Compiled.placeRow
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have e1 : 2 * (a / 2) = a := by omega
    rw [ite_eq_left h, e1, Nat.xor_one_of_even (Nat.even_iff.mpr h)]
  · have e1 : 2 * (a / 2) + 1 = a := by omega
    have e2 : 2 * (a / 2) = a - 1 := by omega
    rw [ite_eq_right (by omega), e1, e2, Nat.xor_one_of_odd (Nat.odd_iff.mpr h)]

/-- The degree bound of a column of level `j` is at most the degree bound of
the level, in logarithms: `n` is the log-height of the first domain, `h` that
of the column, `lb` the log of the blowup and `lfp` the log of the length of
the final polynomial. -/
theorem logDegree_le {n lb lfp j h : ℕ} (hl : h + j = n) :
    h - lb ≤ n - (lb + lfp) - j + lfp := by
  omega

/-- When the final polynomial is a constant, a column of the last level has
the degree bound one, in logarithms. -/
theorem logDegree_eq_zero {n lb lfp h : ℕ} (hlfp : lfp = 0) (hl : h + (n - (lb + lfp)) = n) :
    h - lb = 0 := by
  omega

/-! ## Quotients and sums of polynomials -/

section Poly

variable {K : Type} [Field K]

/-- The value of the quotient `(p - y) / (X - z)` at a point `u` other than
`z`, when `y` is the value of `p` at `z`: the quotient of the values. -/
theorem eval_quotient {p : K[X]} {y z : K} (hy : y = p.eval z) {u : K} (hu : z ≠ u) :
    ((p - C y) /ₘ (X - C z)).eval u = (y - p.eval u) / (z - u) := by
  have hroot : (p - C y).IsRoot z := by rw [IsRoot.def, eval_sub, eval_C, hy, sub_self]
  have hmul := congrArg (eval u) (mul_divByMonic_eq_iff_isRoot.mpr hroot)
  rw [eval_mul, eval_sub, eval_X, eval_C, eval_sub, eval_C] at hmul
  rw [eq_div_iff (sub_ne_zero.mpr hu)]
  linear_combination -hmul

/-- The quotient `(p - y) / (X - z)` respects every positive degree bound that
`p` respects. -/
theorem degree_quotient_lt {p : K[X]} {d : ℕ} (hp : p.degree < d) (hd : 0 < d) (y z : K) :
    ((p - C y) /ₘ (X - C z)).degree < d :=
  (degree_divByMonic_le _ _).trans_lt
    ((degree_sub_le _ _).trans_lt (max_lt hp (degree_C_le.trans_lt (Nat.cast_pos.mpr hd))))

/-- For a constant polynomial `p` and its value `y`, the quotient
`(p - y) / (X - z)` is zero. -/
theorem quotient_eq_zero {p : K[X]} (hp : p.degree < 1) {y z : K} (hy : y = p.eval z) :
    (p - C y) /ₘ (X - C z) = 0 := by
  have hC := eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hp)
  rw [hy, hC, eval_C, sub_self, zero_divByMonic]

/-- A sum of polynomials of degree below `d` has degree below `d`. -/
theorem degree_list_sum_lt {d : ℕ} :
    ∀ l : List K[X], (∀ p ∈ l, p.degree < d) → l.sum.degree < d
  | [], _ => by
    rw [List.sum_nil, degree_zero]
    exact WithBot.bot_lt_coe d
  | p :: l, h => by
    rw [List.sum_cons]
    exact (degree_add_le _ _).trans_lt (max_lt (h p List.mem_cons_self)
      (degree_list_sum_lt l fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-- A sum over a list with positions is the sum over the positions. -/
theorem sum_map_zipIdx {β : Type} (f : β → ℕ → K) (l : List β) (n : ℕ) :
    ((l.zipIdx n).map fun ck => f ck.1 ck.2).sum = ∑ k : Fin l.length, f (l.get k) (n + k) := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih]
    refine Eq.trans ?_
      (Fin.sum_univ_succ fun k : Fin (l.length + 1) => f ((a :: l).get k) (n + k)).symm
    simp [Nat.add_assoc, Nat.add_comm 1]

/-! ## One folding round -/

/-- `Compiled.foldRow` on the values of a polynomial at `x` and at `-x` is the
value of the fold of the polynomial at `x ^ 2`. -/
theorem foldRow_eval (h2 : (2 : K) ≠ 0) (β : K) {x : K} (hx : x ≠ 0) (p : K[X]) :
    Compiled.foldRow β x (p.eval x) (p.eval (-x)) = (foldPoly β p).eval (x ^ 2) := by
  rw [← foldAt_eq_eval_foldPoly h2 (f := fun y => p.eval y) β hx rfl rfl,
    foldAt_eq_interpolate h2 _ β hx]
  rfl

variable {ω : K} {n : ℕ}

/-- A domain point is not zero. -/
theorem pointOfIndex_ne_zero (hω : IsPrimitiveRoot ω (2 ^ n)) (h index : ℕ) :
    pointOfIndex ω n h index ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ (hω.ne_zero (by positivity)))

/-- The two points of a row of level `i` are negations of each other. -/
theorem pointOfIndex_two_mul_add_one_eq_neg (hω : IsPrimitiveRoot ω (2 ^ n)) {i : ℕ} (hi : i < n)
    (q : ℕ) : pointOfIndex ω n (n - i) (2 * q + 1) = -pointOfIndex ω n (n - i) (2 * q) := by
  have e : n - i = n - (i + 1) + 1 := by omega
  rw [e, pointOfIndex_two_mul_add_one hω (by omega), pointOfIndex_two_mul]

/-- The first point of row `q` of level `i` squares to the point of the index
`q` of level `i + 1`. -/
theorem pointOfIndex_two_mul_sq (hω : IsPrimitiveRoot ω (2 ^ n)) {i : ℕ} (hi : i < n) (q : ℕ) :
    pointOfIndex ω n (n - i) (2 * q) ^ 2 = pointOfIndex ω n (n - (i + 1)) q := by
  have e : n - i = n - (i + 1) + 1 := by omega
  rw [e, pointOfIndex_sq hω (by omega), Nat.mul_div_cancel_left _ two_pos]

variable {D : Type} (P : Compiled.Params K) (pf : Compiled.Proof K D P.batches P.queries)
  (msg₀ : Compiled.Msg K D P.batches) (α : K) (β : ℕ → K) (idx : ℕ) (t : Fin P.queries)

/-- If the value of the fold chain after `i` rounds and the sibling value of
round `i` are the values of a polynomial `g` at the query's point of level `i`
and at the other point of its pair, the row of round `i` holds the values of
`g` at the two points of the row. -/
theorem commitRow_of_folded {i : ℕ} (g : K[X])
    (hfold : P.folded pf msg₀ α β idx t i =
      g.eval (pointOfIndex P.ω P.n (P.n - i) (idx >>> i)))
    (hsib : pf.siblings i t = g.eval (pointOfIndex P.ω P.n (P.n - i) ((idx >>> i) ^^^ 1))) :
    P.commitRow pf msg₀ α β idx t i =
      (g.eval (pointOfIndex P.ω P.n (P.n - i) (2 * (idx >>> (i + 1)))),
        g.eval (pointOfIndex P.ω P.n (P.n - i) (2 * (idx >>> (i + 1)) + 1))) := by
  rw [Compiled.Params.commitRow, hfold, hsib, Nat.shiftRight_succ]
  exact placeRow_eq (fun k => g.eval (pointOfIndex P.ω P.n (P.n - i) k)) (idx >>> i)

/-- One round of the fold chain on polynomials: if the row of round `i` holds
the values of `g` at its two points and the reduced opening of level `i + 1` is
the value of `r` at the query's point of that level, the fold chain after
`i + 1` rounds is the value of `foldPoly (β i) g + C (β i ^ 2) * r` there. -/
theorem folded_succ_of_row {i : ℕ} (hi : i < P.n) (g r : K[X])
    (hrow : P.commitRow pf msg₀ α β idx t i =
      (g.eval (pointOfIndex P.ω P.n (P.n - i) (2 * (idx >>> (i + 1)))),
        g.eval (pointOfIndex P.ω P.n (P.n - i) (2 * (idx >>> (i + 1)) + 1))))
    (hred : P.reduced msg₀ (P.opened pf t) α idx (i + 1) =
      r.eval (pointOfIndex P.ω P.n (P.n - (i + 1)) (idx >>> (i + 1)))) :
    P.folded pf msg₀ α β idx t (i + 1) =
      (foldPoly (β i) g + C (β i ^ 2) * r).eval
        (pointOfIndex P.ω P.n (P.n - (i + 1)) (idx >>> (i + 1))) := by
  have h2 : (2 : K) ≠ 0 := Domain.two_ne_zero_of_isPrimitiveRoot P.prim (by omega)
  rw [Compiled.Params.folded_succ, hrow, hred]
  dsimp only
  rw [pointOfIndex_two_mul_add_one_eq_neg P.prim hi,
    foldRow_eval h2 (β i) (pointOfIndex_ne_zero P.prim _ _), pointOfIndex_two_mul_sq P.prim hi,
    eval_add, eval_mul, eval_C]

end Poly

/-! ## The quotient of a claim -/

section Statement

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) {w : Committed F K} {points values : Array EF}

/-- The value of the quotient of a claim at a point of the coset its matrix is
committed on: the quotient the verifier forms from the claimed value, the value
of the column and the opening point. -/
theorem eval_quotientPoly (hst : HonestStatement m params shape wf w points values)
    {c : ClaimRef} (hc : c ∈ claimRefs params.logBlowup shape) (i : ℕ) :
    (quotientPoly m w points values c).eval
        ((modelParams m params shape wf).shift *
          pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            c.logHeight i) =
      (m.ext.toModel (values.getD c.valueIdx 0) -
          (w.poly c.batch c.matrix c.col).eval
            ((modelParams m params shape wf).shift *
              pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
                c.logHeight i)) /
        (m.ext.toModel (points.getD c.pointIdx 0) -
          (modelParams m params shape wf).shift *
            pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
              c.logHeight i) := by
  obtain ⟨p, hp, -, -, hh, -⟩ := mem_claimRefs hc
  refine eval_quotient (hst.value c hc) ?_
  rw [hh]
  exact hst.off_domain p c.pointIdx hp i

/-- The quotient the verifier forms for a claim of level `j`, from the opened
entry of a query whose opened entries are the committed ones, is the value of
the quotient of the claim at the query's point of the coset of the level. -/
theorem quotient_eq_eval_quotientPoly (hst : HonestStatement m params shape wf w points values)
    {rows : Array (Array (Array F))} {idx : ℕ}
    (hrows : ∀ c ∈ claimRefs params.logBlowup shape,
      openedEntry rows c =
        (w.row c.batch c.matrix
          (idx >>> (logMaxHeight params.logBlowup shape - c.logHeight))).getD c.col 0)
    (hidx : idx < 2 ^ logMaxHeight params.logBlowup shape) {j : ℕ} {c : ClaimRef}
    (hc : c ∈ levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j) :
    (m.ext.toModel (values.getD c.valueIdx 0) - m.base.toModel (openedEntry rows c)) /
        (m.ext.toModel (points.getD c.pointIdx 0) -
          (modelParams m params shape wf).shift *
            pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
              ((modelParams m params shape wf).n - j) (idx >>> j)) =
      (quotientPoly m w points values c).eval
        ((modelParams m params shape wf).shift *
          pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - j) (idx >>> j)) := by
  have hcr := mem_claimRefs_of_mem_levelClaims hc
  have hl := logHeight_of_mem_levelClaims hc
  have hlt : idx >>> (logMaxHeight params.logBlowup shape - c.logHeight) < 2 ^ c.logHeight := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.add_sub_cancel' (by omega)]
    exact hidx
  have hn : (modelParams m params shape wf).n - j = c.logHeight := by
    change logMaxHeight params.logBlowup shape - j = c.logHeight
    omega
  have hj : j = logMaxHeight params.logBlowup shape - c.logHeight := by omega
  rw [hn, hj, eval_quotientPoly m params shape wf hst hcr, hrows c hcr,
    hst.row_eval c hcr _ hlt]

/-- The value of `inputPoly` of a level: claim number `k` of the level enters
with `α ^ k`, as the value of its quotient at the shifted point. -/
theorem eval_inputPoly (α : K) (j : ℕ) (x : K) :
    (inputPoly m params shape wf w points values α j).eval x =
      ∑ k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
          j).length,
        α ^ (k : ℕ) * (quotientPoly m w points values
          ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
            k)).eval ((modelParams m params shape wf).shift * x) := by
  rw [inputPoly, eval_listSum, List.map_map]
  refine (sum_map_zipIdx (fun c k => eval x (C (α ^ k) *
    (quotientPoly m w points values c).comp (C (modelParams m params shape wf).shift * X)))
    _ 0).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, Nat.zero_add]

/-- The honest word of level `0` is the polynomial the claims of level `0`
reduce to. -/
theorem honestWord_zero (α : K) (β : ℕ → K) :
    honestWord m params shape wf w points values α β 0 =
      inputPoly m params shape wf w points values α 0 :=
  rfl

/-- The honest word of level `i + 1` is the fold of the honest word of level
`i`, plus `β i ^ 2` times the polynomial the claims of level `i + 1` reduce to. -/
theorem honestWord_succ (α : K) (β : ℕ → K) (i : ℕ) :
    honestWord m params shape wf w points values α β (i + 1) =
      foldPoly (β i) (honestWord m params shape wf w points values α β i) +
        C (β i ^ 2) * inputPoly m params shape wf w points values α (i + 1) :=
  rfl

end Statement

/-! ## The first message, read by the model -/

section FirstMessage

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Inhabited D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) {commitments : Array D} {points values : Array EF}
  {proof : FriProof F EF D (Array (List D)) (Array (List D))}

/-- The opening point of a claim in the statement read by the model is the
entry of `points` the claim refers to. -/
theorem point_firstMessage
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    {j : ℕ} (hj : j ≤ numRounds params shape)
    (k : Fin ((modelParams m params shape wf).numClaims j)) :
    (view m params shape (firstMessage (F := F) commitments points values)).point j k =
      m.ext.toModel (points.getD
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).pointIdx 0) := by
  have hk : ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
      k).pointIdx < (points.toList.map m.ext.toModel).length := by
    rw [List.length_map, Array.length_toList, Arith.size_points hshape]
    exact Arith.pointIdx_lt_of_mem_levelClaims (List.get_mem _ k)
  rw [Arith.view_point m params shape _ hj k, Arith.extsIn_firstMessage,
    List.getD_append _ _ _ _ hk, toModel_getD_toList_map]

/-- The claimed value of a claim in the statement read by the model is the
entry of `values` the claim refers to. -/
theorem value_firstMessage
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    {j : ℕ} (hj : j ≤ numRounds params shape)
    (k : Fin ((modelParams m params shape wf).numClaims j)) :
    (view m params shape (firstMessage (F := F) commitments points values)).value j k =
      m.ext.toModel (values.getD
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).valueIdx 0) := by
  have hlen : (points.toList.map m.ext.toModel).length =
      (pointRefs params.logBlowup shape).length := by
    rw [List.length_map, Array.length_toList, Arith.size_points hshape]
  rw [Arith.view_value m params shape _ hj k, Arith.extsIn_firstMessage, ← hlen,
    List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    toModel_getD_toList_map]

end FirstMessage

end HonestArith

/-! ## The reduced claims of a level -/

section Input

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) {w : Committed F K} {points values : Array EF}

/-- **The reduced claims of a level respect the degree bound of the level.**
For an honest statement, `inputPoly` of every level has degree below the degree
bound of that level in the low-degree test of the model. -/
theorem degree_inputPoly_lt [DecidableEq K]
    (hst : HonestStatement m params shape wf w points values) (α : K) (j : ℕ) :
    (inputPoly m params shape wf w points values α j).degree <
      (modelParams m params shape wf).ldt.degree j := by
  have hpos : 0 < (modelParams m params shape wf).ldt.degree j :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  unfold inputPoly
  refine HonestArith.degree_list_sum_lt _ fun p hp => ?_
  obtain ⟨ck, hck, rfl⟩ := List.mem_map.mp hp
  have hc := List.fst_mem_of_mem_zipIdx hck
  have hl := logHeight_of_mem_levelClaims hc
  refine Fold.degree_C_mul_lt _ (Domain.degree_comp_C_mul_X_lt ?_ _)
  refine HonestArith.degree_quotient_lt
    (lt_of_lt_of_le (hst.degree ck.1 (mem_claimRefs_of_mem_levelClaims hc)) ?_) hpos _ _
  rw [Nat.cast_le]
  change 2 ^ (ck.1.logHeight - params.logBlowup) ≤
    2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen
  rw [← pow_add]
  exact Nat.pow_le_pow_right two_pos (HonestArith.logDegree_le hl)

/-- **The claims of the last level reduce to zero when the final polynomial is
a constant.** A column of the last level is then the codeword of a constant, so
the quotient of each of its claims is zero. -/
theorem inputPoly_numRounds_eq_zero (hst : HonestStatement m params shape wf w points values)
    (hlfp : params.logFinalPolyLen = 0) (α : K) :
    inputPoly m params shape wf w points values α (numRounds params shape) = 0 := by
  unfold inputPoly
  refine List.sum_eq_zero fun p hp => ?_
  obtain ⟨ck, hck, rfl⟩ := List.mem_map.mp hp
  have hc := List.fst_mem_of_mem_zipIdx hck
  have hcr := mem_claimRefs_of_mem_levelClaims hc
  have hl := logHeight_of_mem_levelClaims hc
  have h0 : ck.1.logHeight - params.logBlowup = 0 := HonestArith.logDegree_eq_zero hlfp hl
  have hdeg := hst.degree ck.1 hcr
  rw [h0, pow_zero, Nat.cast_one] at hdeg
  have hq : quotientPoly m w points values ck.1 = 0 :=
    HonestArith.quotient_eq_zero hdeg (hst.value ck.1 hcr)
  rw [hq, zero_comp, mul_zero]

end Input

/-! ## One query of the model verifier -/

section Query

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Inhabited D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) {w : Committed F K} {commitments : Array D}
  {points values : Array EF} {proof : FriProof F EF D (Array (List D)) (Array (List D))}

/-- **The reduced openings of an honest statement.** For a query whose opened
entries are the committed ones, the reduced opening the model verifier computes
at a level `j` up to the last round is the value of `inputPoly` of that level
at the query's point of the level. -/
theorem reduced_eq_eval_inputPoly (hst : HonestStatement m params shape wf w points values)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) (α : K)
    {idx : ℕ} (t : Fin params.numQueries)
    (hrows : ∀ c ∈ claimRefs params.logBlowup shape,
      openedEntry (queryRows proof t.val) c =
        (w.row c.batch c.matrix
          (idx >>> (logMaxHeight params.logBlowup shape - c.logHeight))).getD c.col 0)
    (hidx : idx < 2 ^ logMaxHeight params.logBlowup shape) {j : ℕ}
    (hj : j ≤ numRounds params shape) :
    (modelParams m params shape wf).reduced
        (view m params shape (firstMessage commitments points values))
        ((modelParams m params shape wf).opened (modelProof m params shape proof) t) α idx j =
      (inputPoly m params shape wf w points values α j).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - j) (idx >>> j)) := by
  rw [HonestArith.eval_inputPoly]
  unfold Compiled.Params.reduced
  refine Finset.sum_congr rfl fun k _ => congrArg _ ?_
  have key := HonestArith.quotient_eq_eval_quotientPoly m params shape wf hst hrows hidx
    (List.get_mem (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j) k)
  rw [← HonestArith.point_firstMessage m params shape wf hshape hj k,
    ← HonestArith.value_firstMessage m params shape wf hshape hj k,
    ← opened_modelProof m params shape wf t j k] at key
  exact key

/-- **The fold chain of the model verifier walks the honest words.** For a
query whose opened entries are the committed ones, if the sibling value of
every round before `i` is the value of the honest word of that round at the
other point of the query's pair, the fold chain after `i` rounds is the value
of the honest word of level `i` at the query's point of that level. -/
theorem folded_eq_eval_honestWord (hst : HonestStatement m params shape wf w points values)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) (α : K)
    (β : ℕ → K) {idx : ℕ} (t : Fin params.numQueries)
    (hrows : ∀ c ∈ claimRefs params.logBlowup shape,
      openedEntry (queryRows proof t.val) c =
        (w.row c.batch c.matrix
          (idx >>> (logMaxHeight params.logBlowup shape - c.logHeight))).getD c.col 0)
    (hidx : idx < 2 ^ logMaxHeight params.logBlowup shape) {i : ℕ}
    (hi : i ≤ numRounds params shape)
    (hsib : ∀ r < i, m.ext.toModel (sibling proof r t.val) =
      (honestWord m params shape wf w points values α β r).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - r) ((idx >>> r) ^^^ 1))) :
    (modelParams m params shape wf).folded (modelProof m params shape proof)
        (view m params shape (firstMessage commitments points values)) α β idx t i =
      (honestWord m params shape wf w points values α β i).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - i) (idx >>> i)) := by
  induction i with
  | zero =>
    rw [HonestArith.honestWord_zero]
    exact reduced_eq_eval_inputPoly m params shape wf hst hshape α t hrows hidx (Nat.zero_le _)
  | succ i ih =>
    have hin : i < logMaxHeight params.logBlowup shape := lt_of_lt_of_le hi (Nat.sub_le _ _)
    have hfold := ih (Nat.le_of_succ_le hi) fun r hr => hsib r (Nat.lt_succ_of_lt hr)
    rw [HonestArith.honestWord_succ]
    exact HonestArith.folded_succ_of_row (modelParams m params shape wf)
      (modelProof m params shape proof)
      (view m params shape (firstMessage commitments points values)) α β idx t hin
      (honestWord m params shape wf w points values α β i)
      (inputPoly m params shape wf w points values α (i + 1))
      (HonestArith.commitRow_of_folded (modelParams m params shape wf)
        (modelProof m params shape proof)
        (view m params shape (firstMessage commitments points values)) α β idx t
        (honestWord m params shape wf w points values α β i) hfold (hsib i (Nat.lt_succ_self i)))
      (reduced_eq_eval_inputPoly m params shape wf hst hshape α t hrows hidx hi)

/-- **The rows of the model verifier are the committed rows of the honest
words.** For a query whose opened entries are the committed ones, if the
sibling value of every round up to `i` is the value of the honest word of that
round at the other point of the query's pair, the row the model verifier
reconstructs in round `i` holds the values of the honest word of level `i` at
the points of the indices `2 * p` and `2 * p + 1`, for `p` the position of the
row. -/
theorem commitRow_eq_eval_honestWord (hst : HonestStatement m params shape wf w points values)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) (α : K)
    (β : ℕ → K) {idx : ℕ} (t : Fin params.numQueries)
    (hrows : ∀ c ∈ claimRefs params.logBlowup shape,
      openedEntry (queryRows proof t.val) c =
        (w.row c.batch c.matrix
          (idx >>> (logMaxHeight params.logBlowup shape - c.logHeight))).getD c.col 0)
    (hidx : idx < 2 ^ logMaxHeight params.logBlowup shape) {i : ℕ}
    (hi : i < numRounds params shape)
    (hsib : ∀ r ≤ i, m.ext.toModel (sibling proof r t.val) =
      (honestWord m params shape wf w points values α β r).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - r) ((idx >>> r) ^^^ 1))) :
    (modelParams m params shape wf).commitRow (modelProof m params shape proof)
        (view m params shape (firstMessage commitments points values)) α β idx t i =
      ((honestWord m params shape wf w points values α β i).eval
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - i) (2 * (idx >>> (i + 1)))),
        (honestWord m params shape wf w points values α β i).eval
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - i) (2 * (idx >>> (i + 1)) + 1))) :=
  HonestArith.commitRow_of_folded (modelParams m params shape wf)
    (modelProof m params shape proof)
    (view m params shape (firstMessage commitments points values)) α β idx t
    (honestWord m params shape wf w points values α β i)
    (folded_eq_eval_honestWord m params shape wf hst hshape α β t hrows hidx hi.le
      fun r hr => hsib r hr.le)
    (hsib i le_rfl)

end Query

end CertiFri.Exec
