import CertiFriP3.Pruned
import CertiFriProofs.Exec.CompletenessChecks
import CertiFriProofs.Exec.Stark.SoundnessTensor

/-!
# Soundness of tensor-batched STARKs with Plonky3's pruned MMCS (`CertiFri.P3.prunedMmcs`)

Extends `Exec/Stark/SoundnessTensor.lean` from unpruned `merkleMmcs` (one full
authentication path per query) to Plonky3's `CertiFri.P3.prunedMmcs` (`PrunedPaths D`,
a single flat deduplicated list of sibling digests per multi-opening):

1. **Monadic pruned path restoration (`restorePathsM`):**
   * `run_restorePathsM`: against any oracle function `f`, `(restorePathsM ...).run f`
     equals `CertiFri.P3.restorePaths (hasherOf f) ...`.
   * `queryBound_restorePathsM`: makes at most `indices.size * (3 * maxLogHeight dims + 1)`
     hash queries (identical bound to unpruned `verifyOpeningsM`).
   * `restorePaths_map`: commutes `restorePaths` with entry maps (`m.base.toModel` and
     `m.ext.toModel`), unifying `inputHasher` and `friHasher` with `hasherOf f`.

2. **Pruned tensor shard verification (`shardCompTensorPruned`, `shard_goodTensorPruned`):**
   * After deriving the Fiat–Shamir chain (`deriveA`), runs `restoreShardPathsM` to
     reconstruct the full per-query authentication paths for every input batch and
     folding round, then verifies the restored unpruned `Compiled.Proof` via
     `Compiled.Params.verifyWithTensor`. Total query bound per shard is
     `shardQueriesPruned sys n = 4 + (n + 2) + 2 * ((4 + n) * (numQueries * (3 * n + 1)))`.
   * By `prunedMmcs_accepts`, `rows_queryResultTensor`, and `shard_goodTensor_of_derive_verify`,
     any pruned proof accepted in a good log satisfies every AIR constraint and lookup
     non-vanishing clause with zero proof duplication.

3. **Unconditional unique-decoding ROM soundness theorems for `prunedMmcs`:**
   * `soundness_verifyTensorPruned_ud`
   * `soundness_verifyBatchTensorPruned_ud`
   * `soundness_verifyTensorPruned_lookups_ud`
   * `soundness_verifyBatchTensorPruned_lookups_ud`
-/

namespace CertiFri.Exec.Stark

open CertiFri CertiFri.P3 CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri
  CertiFri.Oracle CertiFri.Oracle.MerkleRO CertiFri.PcsRbr OracleComp Polynomial
open CertiFri.Exec.Transcript (answer)

/-! ## 1. Monadic Pruned Path Restoration (`restorePathsM`) -/

section RestoreM

variable {Msg : Type} {Chal : ℕ → Type} {T D : Type}

/-- Map an oracle computation over a list sequentially, collecting results. -/
def mapM_oc {X : Type*} {Y : X → Type*} {α β : Type*} (f : α → OracleComp Y β) :
    List α → OracleComp Y (List β)
  | [] => .pure []
  | a :: as => (f a).bind fun b => (mapM_oc f as).bind fun bs => .pure (b :: bs)

theorem run_mapM_oc {X : Type*} {Y : X → Type*} {α β : Type*}
    (f : α → OracleComp Y β) (g : ∀ x, Y x) :
    ∀ l : List α, (mapM_oc f l).run g = l.map (fun a => (f a).run g)
  | [] => rfl
  | a :: as => by
    simp only [mapM_oc, run_bind, run_pure, List.map_cons, run_mapM_oc f g as]

theorem queryBound_mapM_oc {X : Type*} {Y : X → Type*} {α β : Type*}
    {f : α → OracleComp Y β} {q : ℕ} (hf : ∀ a, (f a).QueryBound q) :
    ∀ l : List α, (mapM_oc f l).QueryBound (l.length * q)
  | [] => by simp [mapM_oc]
  | a :: as => by
    unfold mapM_oc
    refine (QueryBound.bind (hf a) fun b =>
      QueryBound.bind (queryBound_mapM_oc hf as) fun bs =>
        queryBound_pure (b :: bs) 0).mono ?_
    simp [Nat.succ_mul]; omega

/-- Monadic version of `Pruned.leaves`. -/
def leavesM (dims : List Dimensions) (top : ℕ)
    (queries : List (ℕ × List (Array T))) :
    OracleComp (MerkleAnswer Msg Chal T D) (List (Pruned.Node T D)) :=
  let ascending := queries.mergeSort fun a b => a.1 ≤ b.1
  let uniq := ascending.eraseRepsBy fun a b => a.1 == b.1
  mapM_oc (fun (index, rows) =>
    (groupDigestM (Msg := Msg) (Chal := Chal) dims rows top).bind fun digest =>
      .pure { index, rows, digest, below := [(index, [])] }) uniq

theorem run_leavesM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) (top : ℕ)
    (queries : List (ℕ × List (Array T))) :
    (leavesM dims top queries).run f = Pruned.leaves (hasherOf f) dims top queries := by
  unfold leavesM Pruned.leaves
  rw [run_mapM_oc]
  apply List.map_congr_left
  intro p _
  rcases p with ⟨index, rows⟩
  simp [run_bind, run_pure, run_groupDigestM]

private lemma length_eraseRepsBy_le {α : Type*} (r : α → α → Bool) :
    ∀ l : List α, (l.eraseRepsBy r).length ≤ l.length := by
  suffices ∀ (a : α) (l : List α), (List.eraseRepsBy.loop r a l []).length ≤ l.length + 1 by
    intro l
    cases l with
    | nil => simp [List.eraseRepsBy]
    | cons a l => simpa [List.eraseRepsBy] using this a l
  suffices ∀ (a : α) (l acc : List α),
      (List.eraseRepsBy.loop r a l acc).length ≤ l.length + acc.length + 1 by
    intro a l; simpa using this a l []
  intro a l
  induction l generalizing a with
  | nil => intro acc; simp [List.eraseRepsBy.loop]
  | cons b bs ih =>
    intro acc
    unfold List.eraseRepsBy.loop
    split
    · have h := ih a acc; simp; omega
    · have h := ih b (a :: acc); simp at h ⊢; omega

theorem queryBound_leavesM (dims : List Dimensions) (top : ℕ)
    (queries : List (ℕ × List (Array T))) :
    (leavesM (Msg := Msg) (Chal := Chal) (D := D) dims top queries).QueryBound queries.length := by
  unfold leavesM
  dsimp only
  have h1 := queryBound_mapM_oc (q := 1)
    (f := fun p : ℕ × List (Array T) =>
      (groupDigestM (Msg := Msg) (Chal := Chal) (D := D) dims p.2 top).bind fun digest =>
        .pure ({ index := p.1, rows := p.2, digest, below := [(p.1, [])] } : Pruned.Node T D))
    (fun p => by
      unfold groupDigestM hashRowsM
      exact (QueryBound.bind (queryBound_query (Y := MerkleAnswer Msg Chal T D) _) fun _ =>
        queryBound_pure _ 0).mono (by omega))
    ((queries.mergeSort fun a b => a.1 ≤ b.1).eraseRepsBy fun a b => a.1 == b.1)
  have hlen : ((queries.mergeSort fun a b => a.1 ≤ b.1).eraseRepsBy fun a b => a.1 == b.1).length ≤
      queries.length := by
    calc _ ≤ (queries.mergeSort fun a b => a.1 ≤ b.1).length := length_eraseRepsBy_le _ _
      _ = queries.length := List.length_mergeSort _
  exact h1.mono (by omega)

/-- Monadic version of `Pruned.Node.parent`. -/
def nodeParentM (dims : List Dimensions) (h : ℕ) (node : Pruned.Node T D)
    (sibling : D) (belowSibling : List (ℕ × List D)) :
    OracleComp (MerkleAnswer Msg Chal T D) (Pruned.Node T D) :=
  (parentM (Msg := Msg) (Chal := Chal) node.index node.digest sibling).bind fun p =>
    (injectM dims node.rows h p).bind fun d =>
      .pure { index := node.index / 2
              digest := d
              rows := node.rows
              below := Pruned.addSibling sibling node.below ++ belowSibling }

theorem run_nodeParentM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) (h : ℕ)
    (node : Pruned.Node T D) (sibling : D) (belowSibling : List (ℕ × List D)) :
    (nodeParentM dims h node sibling belowSibling).run f =
      node.parent (hasherOf f) dims h sibling belowSibling := by
  simp [nodeParentM, Pruned.Node.parent, run_bind, run_pure, run_parentM, run_injectM]

theorem queryBound_nodeParentM (dims : List Dimensions) (h : ℕ)
    (node : Pruned.Node T D) (sibling : D) (belowSibling : List (ℕ × List D)) :
    (nodeParentM (Msg := Msg) (Chal := Chal) dims h node sibling belowSibling).QueryBound 3 := by
  unfold nodeParentM
  have hp : (parentM (Msg := Msg) (Chal := Chal) (T := T) node.index node.digest sibling).QueryBound 1 := by
    unfold parentM compressM
    by_cases hpar : node.index % 2 = 0
    · simp only [hpar, ↓reduceIte]; exact queryBound_query (Y := MerkleAnswer Msg Chal T D) _
    · simp only [hpar, ↓reduceIte]; exact queryBound_query (Y := MerkleAnswer Msg Chal T D) _
  have hi : ∀ p, (injectM (Msg := Msg) (Chal := Chal) dims node.rows h p).QueryBound 2 := fun p => by
    unfold injectM
    split_ifs
    · have hq1 : (groupDigestM (Msg := Msg) (Chal := Chal) (D := D) dims node.rows h).QueryBound 1 :=
        queryBound_query (Y := MerkleAnswer Msg Chal T D) _
      have hq2 : ∀ g, (compressM (Msg := Msg) (Chal := Chal) (T := T) p g).QueryBound 1 := fun _ =>
        queryBound_query (Y := MerkleAnswer Msg Chal T D) _
      exact (QueryBound.bind hq1 hq2).mono (by omega)
    · exact queryBound_pure _ 2
  exact (QueryBound.bind hp fun p =>
    QueryBound.bind (hi p) fun _ => queryBound_pure _ 0).mono (by omega)

/-- Monadic version of `Pruned.ascend`. -/
def ascendM (dims : List Dimensions) (h : ℕ) :
    List (Pruned.Node T D) → List D →
      OracleComp (MerkleAnswer Msg Chal T D) (Option (List (Pruned.Node T D) × List D))
  | [], supplied => .pure (some ([], supplied))
  | node :: nodes, supplied =>
    match nodes with
    | next :: rest =>
      if node.index / 2 = next.index / 2 then
        (ascendM dims h rest supplied).bind fun res =>
          match res with
          | none => .pure none
          | some (parents, supplied') =>
            let below := Pruned.addSibling node.digest next.below
            (nodeParentM dims h node next.digest below).bind fun p =>
              .pure (some (p :: parents, supplied'))
      else
        match supplied with
        | [] => .pure none
        | sibling :: supplied =>
          (ascendM dims h (next :: rest) supplied).bind fun res =>
            match res with
            | none => .pure none
            | some (parents, supplied') =>
              (nodeParentM dims h node sibling []).bind fun p =>
                .pure (some (p :: parents, supplied'))
    | [] =>
      match supplied with
      | [] => .pure none
      | sibling :: supplied =>
        (nodeParentM dims h node sibling []).bind fun p =>
          .pure (some ([p], supplied))

theorem run_ascendM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D),
      (ascendM dims h nodes supplied).run f = Pruned.ascend (hasherOf f) dims h nodes supplied
  | [], supplied => by simp [ascendM, Pruned.ascend]
  | [node], [] => by simp [ascendM, Pruned.ascend]
  | [node], sibling :: supplied => by
    simp [ascendM, Pruned.ascend, run_bind, run_pure, run_nodeParentM]
  | node :: next :: rest, supplied => by
    unfold ascendM Pruned.ascend
    dsimp only
    split_ifs with heq
    · rw [run_bind, run_ascendM f dims h rest supplied]
      cases Pruned.ascend (hasherOf f) dims h rest supplied with
      | none => rfl
      | some ps =>
        rcases ps with ⟨parents, supplied'⟩
        simp [run_bind, run_pure, run_nodeParentM]
    · cases supplied with
      | nil => rfl
      | cons sibling supplied =>
        dsimp only
        rw [run_bind, run_ascendM f dims h (next :: rest) supplied]
        cases Pruned.ascend (hasherOf f) dims h (next :: rest) supplied with
        | none => rfl
        | some ps =>
          rcases ps with ⟨parents, supplied'⟩
          simp [run_bind, run_pure, run_nodeParentM]

theorem queryBound_ascendM (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D),
      (ascendM (Msg := Msg) (Chal := Chal) dims h nodes supplied).QueryBound (3 * nodes.length) := by
  intro nodes
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes with
  | h n ih =>
    intro supplied
    cases nodes with
    | nil => simp [ascendM]
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => exact queryBound_pure _ _
        | cons s ss =>
          unfold ascendM; dsimp only
          exact (QueryBound.bind (queryBound_nodeParentM dims h node s []) fun _ =>
            queryBound_pure _ 0).mono (by simp at hn; omega)
      | cons next tail =>
        unfold ascendM; dsimp only
        split_ifs with heq
        · refine (QueryBound.bind (m := 3)
            (ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl supplied)
            fun res => ?_).mono (by simp only [List.length_cons] at hn; omega)
          cases res with
          | none => exact queryBound_pure _ 3
          | some ps =>
            exact (QueryBound.bind (queryBound_nodeParentM dims h node next.digest _) fun _ =>
              queryBound_pure _ 0).mono (by omega)
        · cases supplied with
          | nil => exact queryBound_pure _ _
          | cons s ss =>
            refine (QueryBound.bind (m := 3)
              (ih (next :: tail).length (by simp only [List.length_cons] at hn ⊢; omega)
                (next :: tail) rfl ss)
              fun res => ?_).mono (by simp only [List.length_cons] at hn ⊢; omega)
            cases res with
            | none => exact queryBound_pure _ 3
            | some ps =>
              exact (QueryBound.bind (queryBound_nodeParentM dims h node s []) fun _ =>
                queryBound_pure _ 0).mono (by omega)

/-- Monadic version of `Pruned.walk`, guarding frontier-size monotonicity so its
`OracleComp.QueryBound` holds structurally across all branches. -/
def walkM (dims : List Dimensions) :
    (h : ℕ) → List (Pruned.Node T D) → List D →
      OracleComp (MerkleAnswer Msg Chal T D) (Option (List (Pruned.Node T D) × List D))
  | 0, nodes, supplied => .pure (some (nodes, supplied))
  | h + 1, nodes, supplied =>
    (ascendM dims h nodes supplied).bind fun res =>
      match res with
      | none => .pure none
      | some (parents, supplied') =>
        if parents.length ≤ nodes.length then walkM dims h parents supplied'
        else .pure none

private theorem ascend_length_le (H : MerkleHasher T D) (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D)
      {parents : List (Pruned.Node T D)} {rem : List D},
      Pruned.ascend H dims h nodes supplied = some (parents, rem) →
      parents.length ≤ nodes.length := by
  intro nodes
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes with
  | h n ih =>
    intro supplied parents rem heq
    cases nodes with
    | nil =>
      simp only [Pruned.ascend, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, _⟩ := heq; omega
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => simp [Pruned.ascend] at heq
        | cons s ss =>
          simp only [Pruned.ascend, Pure.pure, Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, _⟩ := heq; simp at hn ⊢; omega
      | cons next tail =>
        unfold Pruned.ascend at heq
        dsimp only at heq
        split_ifs at heq with hpair
        · cases hrec : Pruned.ascend H dims h tail supplied with
          | none => simp [hrec] at heq
          | some ps =>
            rw [hrec] at heq; simp at heq; obtain ⟨rfl, _⟩ := heq
            have hle := ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl supplied hrec
            simp only [List.length_cons] at hn ⊢; omega
        · cases supplied with
          | nil => simp at heq
          | cons s ss =>
            dsimp only at heq
            cases hrec : Pruned.ascend H dims h (next :: tail) ss with
            | none => simp [hrec] at heq
            | some ps =>
              rw [hrec] at heq; simp at heq; obtain ⟨rfl, _⟩ := heq
              have hle := ih (next :: tail).length
                (by simp only [List.length_cons] at hn ⊢; omega) (next :: tail) rfl ss hrec
              simp only [List.length_cons] at hn hle ⊢; omega

theorem run_walkM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) :
    ∀ (h : ℕ) (nodes : List (Pruned.Node T D)) (supplied : List D),
      (walkM dims h nodes supplied).run f = Pruned.walk (hasherOf f) dims h nodes supplied
  | 0, _, _ => rfl
  | h + 1, nodes, supplied => by
    unfold walkM Pruned.walk
    rw [run_bind, run_ascendM]
    cases hres : Pruned.ascend (hasherOf f) dims h nodes supplied with
    | none => rfl
    | some ps =>
      have hle := ascend_length_le (hasherOf f) dims h nodes supplied hres
      simp only [hle, ↓reduceIte]
      exact run_walkM f dims h ps.1 ps.2

/-- Monadic version of `CertiFri.P3.restorePaths`. -/
def restorePathsM (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    OracleComp (MerkleAnswer Msg Chal T D) (Option (Array (List D))) :=
  if dims.isEmpty || openedRows.size != indices.size then .pure none
  else
    let top := Merkle.maxLogHeight dims.toList
    let queries := indices.toList.zip (openedRows.toList.map (·.toList))
    (leavesM dims.toList top queries).bind fun lvs =>
      if lvs.length ≤ indices.size then
        (walkM dims.toList top lvs proof.siblingHashes.toList).bind fun res =>
          match res with
          | some (nodes, []) =>
            let found := nodes.flatMap (·.below)
            .pure (indices.mapM fun index => (found.lookup index).map List.reverse)
          | _ => .pure none
      else .pure none

theorem run_restorePathsM (f : ∀ x, MerkleAnswer Msg Chal T D x)
    (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    (restorePathsM dims indices openedRows proof).run f =
      CertiFri.P3.restorePaths (hasherOf f) dims indices openedRows proof := by
  unfold restorePathsM CertiFri.P3.restorePaths
  split_ifs with h
  · rfl
  · rw [run_bind, run_leavesM]
    have hlvs_le : (Pruned.leaves (hasherOf f) dims.toList (Merkle.maxLogHeight dims.toList)
        (indices.toList.zip (openedRows.toList.map (·.toList)))).length ≤ indices.size := by
      unfold Pruned.leaves
      rw [List.length_map]
      have h1 := length_eraseRepsBy_le (fun a b : ℕ × List (Array T) => a.1 == b.1)
        ((indices.toList.zip (openedRows.toList.map (·.toList))).mergeSort fun a b => a.1 ≤ b.1)
      have h2 := List.length_mergeSort (indices.toList.zip (openedRows.toList.map (·.toList)))
        (le := fun a b => a.1 ≤ b.1)
      have h3 : (indices.toList.zip (openedRows.toList.map (·.toList))).length ≤ indices.size := by
        rw [List.length_zip]; simp
      omega
    simp only [hlvs_le, ↓reduceIte, run_bind, run_walkM]
    cases Pruned.walk (hasherOf f) dims.toList (Merkle.maxLogHeight dims.toList)
        (Pruned.leaves (hasherOf f) dims.toList (Merkle.maxLogHeight dims.toList)
          (indices.toList.zip (openedRows.toList.map (·.toList))))
        proof.siblingHashes.toList with
    | none => rfl
    | some ps =>
      rcases ps with ⟨nodes, rem⟩
      cases rem <;> rfl

theorem queryBound_walkM (dims : List Dimensions) (q : ℕ) :
    ∀ (h : ℕ) (nodes : List (Pruned.Node T D)) (supplied : List D),
      nodes.length ≤ q →
      (walkM (Msg := Msg) (Chal := Chal) dims h nodes supplied).QueryBound (3 * h * q) := by
  intro h
  induction h with
  | zero => intro nodes supplied _; simp [walkM]
  | succ h ih =>
    intro nodes supplied hle
    unfold walkM
    have hasc : (ascendM (Msg := Msg) (Chal := Chal) dims h nodes supplied).QueryBound (3 * q) :=
      (queryBound_ascendM dims h nodes supplied).mono (by omega)
    refine (QueryBound.bind (m := 3 * h * q) hasc fun res => ?_).mono (by ring_nf; omega)
    cases res with
    | none => exact queryBound_pure _ (3 * h * q)
    | some ps =>
      dsimp only
      split_ifs with hps
      · exact ih ps.1 ps.2 (hps.trans hle)
      · exact queryBound_pure _ (3 * h * q)

theorem queryBound_restorePathsM (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    (restorePathsM (Msg := Msg) (Chal := Chal) dims indices openedRows proof).QueryBound
      (indices.size * (3 * Merkle.maxLogHeight dims.toList + 1)) := by
  unfold restorePathsM
  split_ifs with h
  · exact queryBound_pure _ _
  · have hqlen : (indices.toList.zip (openedRows.toList.map (·.toList))).length ≤ indices.size := by
      rw [List.length_zip]; simp
    have hlv := (queryBound_leavesM (Msg := Msg) (Chal := Chal) (D := D)
      dims.toList (Merkle.maxLogHeight dims.toList)
      (indices.toList.zip (openedRows.toList.map (·.toList)))).mono hqlen
    refine (QueryBound.bind (m := 3 * Merkle.maxLogHeight dims.toList * indices.size) hlv
      fun lvs => ?_).mono (by ring_nf; omega)
    split_ifs with hlvs
    · exact (QueryBound.bind (m := 0)
        (queryBound_walkM dims.toList indices.size (Merkle.maxLogHeight dims.toList)
          lvs proof.siblingHashes.toList hlvs)
        fun res => by
          cases res with
          | none => exact queryBound_pure _ 0
          | some ps => rcases ps with ⟨nodes, rem⟩; cases rem <;> exact queryBound_pure _ 0).mono
        (by omega)
    · exact queryBound_pure _ _

end RestoreM

/-! ## 2. Pruned Path Restoration Under Entry Maps (`restorePaths_map`) -/

section RestoreMap

private def mapNode {T U D : Type} (g : T → U) (n : Pruned.Node T D) : Pruned.Node U D :=
  { n with rows := n.rows.map (·.map g) }

private lemma eraseRepsBy_map {α β : Type*} (f : α → β) (r : α → α → Bool) (s : β → β → Bool)
    (h : ∀ a b, s (f a) (f b) = r a b) :
    ∀ l : List α, (l.map f).eraseRepsBy s = (l.eraseRepsBy r).map f := by
  have hloop : ∀ (a : α) (l acc : List α),
      List.eraseRepsBy.loop s (f a) (l.map f) (acc.map f) =
        (List.eraseRepsBy.loop r a l acc).map f := by
    intro a l
    induction l generalizing a with
    | nil => intro acc; simp [List.eraseRepsBy.loop, List.map_reverse]
    | cons b bs ih =>
      intro acc
      simp only [List.map_cons]
      unfold List.eraseRepsBy.loop
      rw [h a b]
      cases r a b
      · simpa only [List.map_cons] using ih b (a :: acc)
      · exact ih a acc
  intro l
  cases l with
  | nil => rfl
  | cons a as =>
    simp only [List.map_cons, List.eraseRepsBy]
    simpa only [List.map_nil] using hloop a as []

private lemma leaves_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) (top : ℕ) (queries : List (ℕ × List (Array T))) :
    Pruned.leaves H dims top (queries.map fun p => (p.1, p.2.map (·.map g))) =
      (Pruned.leaves ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims top queries).map
        (mapNode g) := by
  unfold Pruned.leaves; dsimp only
  have hsort := (List.map_mergeSort
    (f := fun p : ℕ × List (Array T) => (p.1, p.2.map (·.map g)))
    (r := fun a b => decide (a.1 ≤ b.1)) (s := fun a b => decide (a.1 ≤ b.1))
    (l := queries) (fun _ _ _ _ => rfl)).symm
  rw [hsort, eraseRepsBy_map (f := fun p : ℕ × List (Array T) => (p.1, p.2.map (·.map g)))
    (r := fun a b => a.1 == b.1) (s := fun a b => a.1 == b.1) (fun _ _ => rfl),
    List.map_map, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_def, mapNode, Exec.Checks.groupDigest_map]

private lemma nodeParent_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) (h : ℕ) (node : Pruned.Node T D)
    (sibling : D) (belowSibling : List (ℕ × List D)) :
    (mapNode g node).parent H dims h sibling belowSibling =
      mapNode g (node.parent ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h sibling belowSibling) := by
  simp only [Pruned.Node.parent, mapNode, Exec.Checks.parent_map, Exec.Checks.inject_map]

private lemma ascend_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D),
      Pruned.ascend H dims h (nodes.map (mapNode g)) supplied =
        (Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h nodes supplied).map
          (fun ps => (ps.1.map (mapNode g), ps.2)) := by
  intro nodes
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes with
  | h n ih =>
    intro supplied
    cases nodes with
    | nil => simp [Pruned.ascend]
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => simp [Pruned.ascend]
        | cons s ss =>
          simp only [List.map_cons, List.map_nil, Pruned.ascend, Pure.pure,
            Option.map_some, nodeParent_map]
      | cons next tail =>
        simp only [List.map_cons]
        unfold Pruned.ascend
        dsimp only [mapNode]
        by_cases heq : node.index / 2 = next.index / 2
        · simp only [heq, ↓reduceIte]
          have hrec := ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl supplied
          rw [hrec]
          cases Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h tail supplied with
          | none => rfl
          | some ps =>
            simp only [Option.map_some, Bind.bind, Option.bind_some, Pure.pure, List.map_cons]
            exact congrArg some (congrArg (·, ps.2) (congrArg (· :: _)
              (nodeParent_map g H dims h node next.digest (Pruned.addSibling node.digest next.below))))
        · simp only [heq, ↓reduceIte]
          cases supplied with
          | nil => rfl
          | cons s ss =>
            dsimp only
            have hrec := ih (next :: tail).length
              (by simp only [List.length_cons] at hn ⊢; omega) (next :: tail) rfl ss
            simp only [List.map_cons] at hrec
            change (do
                let __x ← Pruned.ascend H dims h (mapNode g next :: tail.map (mapNode g)) ss
                Pure.pure (Pruned.Node.parent H dims h (mapNode g node) s [] :: __x.1, __x.2)) = _
            rw [hrec]
            cases Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h (next :: tail) ss with
            | none => rfl
            | some ps =>
              simp only [Option.map_some, Bind.bind, Option.bind_some, Pure.pure, List.map_cons,
                nodeParent_map]

private lemma walk_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) :
    ∀ (h : ℕ) (nodes : List (Pruned.Node T D)) (supplied : List D),
      Pruned.walk H dims h (nodes.map (mapNode g)) supplied =
        (Pruned.walk ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h nodes supplied).map
          (fun ps => (ps.1.map (mapNode g), ps.2))
  | 0, _, _ => rfl
  | h + 1, nodes, supplied => by
    unfold Pruned.walk
    rw [ascend_map]
    cases Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h nodes supplied with
    | none => rfl
    | some ps =>
      simp only [Option.map_some]
      exact walk_map g H dims h ps.1 ps.2

/-- **`restorePaths` commutes with entry maps.** -/
theorem restorePaths_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    CertiFri.P3.restorePaths ⟨fun xs => H.hashRows (xs.map g), H.compress⟩
        dims indices openedRows proof =
      CertiFri.P3.restorePaths H dims indices
        (openedRows.map fun r => r.map fun row => row.map g) proof := by
  unfold CertiFri.P3.restorePaths
  simp only [Array.size_map]
  split_ifs with h
  · rfl
  · have hzip : indices.toList.zip ((openedRows.map fun r => r.map fun row => row.map g).toList.map (·.toList)) =
        (indices.toList.zip (openedRows.toList.map (·.toList))).map
          (fun p => (p.1, p.2.map (·.map g))) := by
      rw [Array.toList_map, List.map_map]
      clear h
      generalize openedRows.toList = rs
      generalize indices.toList = is
      induction is generalizing rs with
      | nil => simp
      | cons i is ih =>
        cases rs with
        | nil => simp
        | cons r rs =>
          simp only [List.map_cons, List.zip_cons_cons]
          rw [ih]
          simp only [Function.comp_def, Array.toList_map]
    rw [hzip, leaves_map, walk_map]
    cases Pruned.walk ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims.toList
        (Merkle.maxLogHeight dims.toList)
        (Pruned.leaves ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims.toList
          (Merkle.maxLogHeight dims.toList) (indices.toList.zip (openedRows.toList.map (·.toList))))
        proof.siblingHashes.toList with
    | none => rfl
    | some ps =>
      rcases ps with ⟨nodes, rem⟩
      cases rem with
      | cons _ _ => rfl
      | nil =>
        simp only [Option.map_some]
        have hflat : (nodes.map (mapNode g)).flatMap (·.below) = nodes.flatMap (·.below) := by
          rw [List.flatMap_map]; rfl
        rw [hflat]

end RestoreMap

/-! ## 3. Pruned Tensor STARK Attempts, Unpruning & Soundness -/

section PrunedStark

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {fslots slots width : ℕ}

/-- Single-shard adversary attempt using `CertiFri.P3.prunedMmcs` (`PrunedPaths D`). -/
structure SAttemptPruned (F EF D : Type) where
  claims : Array (Array F)
  proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)

/-- Multi-shard batch attempt using `CertiFri.P3.prunedMmcs` (`PrunedPaths D`). -/
abbrev BAttemptPruned (F EF D : Type) : Type :=
  BatchProof F EF D (PrunedPaths D) (PrunedPaths D)

/-- Preamble of a single-shard pruned attempt. -/
def SAttemptPruned.preamble (a : SAttemptPruned F EF D) : BatchPreamble F D :=
  ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩

/-- Replace the pruned Merkle proofs in a STARK proof with explicit per-query path arrays. -/
def _root_.CertiFri.Stark.Proof.withPaths (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (inPaths comPaths : Array (Array (List D))) :
    Proof F EF D (Array (List D)) (Array (List D)) where
  active := proof.active
  stage1Commit := proof.stage1Commit
  stage2Commit := proof.stage2Commit
  quotientCommit := proof.quotientCommit
  intermediateAccumulators := proof.intermediateAccumulators
  logDegrees := proof.logDegrees
  quotientOpened := proof.quotientOpened
  preprocessedOpened := proof.preprocessedOpened
  stage1Opened := proof.stage1Opened
  stage2Opened := proof.stage2Opened
  openingProof :=
    { commitPhaseCommits := proof.openingProof.commitPhaseCommits
      commitPowWitnesses := proof.openingProof.commitPowWitnesses
      inputOpenings := proof.openingProof.inputOpenings.mapIdx fun i o =>
        { openedValues := o.openedValues, openingProof := inPaths.getD i #[] }
      commitPhaseOpenings := proof.openingProof.commitPhaseOpenings.mapIdx fun i o =>
        { logArity := o.logArity
          siblingValues := o.siblingValues
          openingProof := comPaths.getD i #[] }
      finalPoly := proof.openingProof.finalPoly
      queryPowWitness := proof.openingProof.queryPowWitness }

/-- Single-shard pruned attempt coverage bounds. -/
structure CoveredPruned (B : Bounds) (a : SAttemptPruned F EF D) : Prop where
  claims : a.claims.size ≤ B.claims
  claim_len : ∀ c ∈ a.claims, c.size ≤ B.len

/-- Multi-shard pruned batch coverage bounds. -/
structure BatchCoveredPruned (B : Bounds) (a : BAttemptPruned F EF D) : Prop where
  shards : a.preamble.headers.size ≤ B.shards
  claims : ∀ h ∈ a.preamble.headers, h.claims.size ≤ B.claims ∧ ∀ c ∈ h.claims, c.size ≤ B.len
  messages : a.preamble.messages.size ≤ B.messages
  message_len : ∀ m ∈ a.preamble.messages, m.args.size ≤ B.len

/-- Query bound for one pruned tensor STARK shard: Fiat–Shamir chain (`4 + (n + 2)`) plus
`2x` Merkle hash queries (once to restore pruned paths, once to verify the restored proof). -/
def shardQueriesPruned (sys : System F D) (n : ℕ) : ℕ :=
  4 + (n + 2) + 2 * ((4 + n) * (sys.fri.numQueries * (3 * n + 1)))

variable (M : StarkModel F EF K) (sys : System F D)

/-- Monadic restoration of all input and folding-round pruned paths for one tensor shard. -/
noncomputable def restoreShardPathsM (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F))
    (t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width)
      (4 + ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2))) :
    OracleComp (STAns F EF D K fslots slots width)
      (Option (Array (Array (List D)) × Array (Array (List D)))) :=
  let shape := starkShape sys M.extData.d pproof.active pproof.logDegrees
  let P := modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)
  let W := maxWidth shape
  let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
  let basePf := modelProof M.toFieldModel sys.fri shape (pproof.withPaths #[] #[]).openingProof
  let ζ := rep M (tFieldAt (chalsOf t) 3)
  let msg0 := view M.toFieldModel sys.fri shape
    (messages sys.fri shape
      ((openingClaims sys pproof ζ).map (·.commitment))
      (claimPoints (openingClaims sys pproof ζ))
      (claimValues (openingClaims sys pproof ζ)) pproof.openingProof 0)
  let rT := tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4)
  let β := fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0
  let idx := fun k : Fin P.queries => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
    (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n
  let inComp := mapM_oc (fun b : Fin P.batches =>
    let dims := P.dims b
    let indices := Array.ofFn fun k : Fin P.queries =>
      idx k >>> (P.n - Merkle.maxLogHeight dims.toList)
    let rows := Array.ofFn (basePf.inputRows b)
    let ppr : PrunedPaths D :=
      match pproof.openingProof.inputOpenings[b.val]? with
      | some o => o.openingProof
      | none => ⟨#[]⟩
    restorePathsM (Msg := RawMsg F EF D) (Chal := UTensorChal K fslots slots width)
      dims indices rows ppr) (List.finRange P.batches)
  let comComp := mapM_oc (fun i : ℕ =>
    let dims := P.commitDims i
    let indices := Array.ofFn fun k : Fin P.queries => idx k >>> (i + 1)
    let rows := Array.ofFn fun k : Fin P.queries =>
      #[#[(P.commitRowTensor W Mopen (tensorCoord sys.fri shape) basePf msg0 rT β (idx k) k i).1,
          (P.commitRowTensor W Mopen (tensorCoord sys.fri shape) basePf msg0 rT β (idx k) k i).2]]
    let ppr : PrunedPaths D :=
      match pproof.openingProof.commitPhaseOpenings[i]? with
      | some o => o.openingProof
      | none => ⟨#[]⟩
    restorePathsM (Msg := RawMsg F EF D) (Chal := UTensorChal K fslots slots width)
      dims indices rows ppr) (List.range P.rounds)
  inComp.bind fun inOpts =>
    comComp.bind fun comOpts =>
      match inOpts.mapM id, comOpts.mapM id with
      | some inPaths, some comPaths => .pure (some (inPaths.toArray, comPaths.toArray))
      | _, _ => .pure none

/-- **The oracle queries of verifying one pruned tensor-batched STARK shard:**
derive the Fiat–Shamir chain, restore all pruned Merkle paths via `restoreShardPathsM`,
and verify the restored unpruned proof via `Compiled.Params.verifyWithTensor`. -/
noncomputable def shardCompTensorPruned (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (m0 mid : RawMsg F EF D) : OracleComp (STAns F EF D K fslots slots width) Bool :=
  if h : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F) then
    let shape := starkShape sys M.extData.d pproof.active pproof.logDegrees
    let P := modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ h)
    let W := maxWidth shape
    let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
    (deriveA (fun _ : HashQuery K D => D)
      (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) (4 + (P.rounds + 2))).bind fun t =>
      (restoreShardPathsM M sys pproof h t).bind fun opt =>
        match opt with
        | some (inPaths, comPaths) =>
          let proof := pproof.withPaths inPaths comPaths
          P.verifyWithTensor W Mopen (tensorCoord sys.fri shape)
            (modelProof M.toFieldModel sys.fri shape proof.openingProof)
            (fun j => view M.toFieldModel sys.fri shape
              (messages sys.fri shape
                ((openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))).map (·.commitment))
                (claimPoints (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
                (claimValues (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
                proof.openingProof j))
            (tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4))
            (fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0)
            (fun k => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
              (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n)
        | none => .pure false
  else .pure false

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] in
private theorem length_starkShape_leP (d : ℕ) (active : Array Bool) (logDegrees : Array ℕ) :
    (starkShape sys d active logDegrees).length ≤ 4 := by
  unfold starkShape
  cases sys.preprocessedCommit <;> exact Nat.le_of_ble_eq_true rfl

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
theorem queryBound_restoreShardPathsM (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F))
    (t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width)
      (4 + ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2))) :
    (restoreShardPathsM M sys pproof htwo t).QueryBound
      (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).verifierQueries := by
  unfold restoreShardPathsM
  dsimp only
  refine (QueryBound.bind
    (n := (modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d pproof.active pproof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).batches *
      ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).queries *
        (3 * (modelParams M.toFieldModel sys.fri
          (starkShape sys M.extData.d pproof.active pproof.logDegrees)
          (M.wellFormed sys.fri _ htwo)).n + 1)))
    (m := (modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d pproof.active pproof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).rounds *
      ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).queries *
        (3 * (modelParams M.toFieldModel sys.fri
          (starkShape sys M.extData.d pproof.active pproof.logDegrees)
          (M.wellFormed sys.fri _ htwo)).n + 1)) + 0)
    ?_ fun inOpts =>
      QueryBound.bind
        (n := (modelParams M.toFieldModel sys.fri
          (starkShape sys M.extData.d pproof.active pproof.logDegrees)
          (M.wellFormed sys.fri _ htwo)).rounds *
          ((modelParams M.toFieldModel sys.fri
            (starkShape sys M.extData.d pproof.active pproof.logDegrees)
            (M.wellFormed sys.fri _ htwo)).queries *
            (3 * (modelParams M.toFieldModel sys.fri
              (starkShape sys M.extData.d pproof.active pproof.logDegrees)
              (M.wellFormed sys.fri _ htwo)).n + 1)))
        (m := 0)
        ?_ fun comOpts => ?_).mono ?_
  · refine (queryBound_mapM_oc
      (q := (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).queries *
        (3 * (modelParams M.toFieldModel sys.fri
          (starkShape sys M.extData.d pproof.active pproof.logDegrees)
          (M.wellFormed sys.fri _ htwo)).n + 1))
      (fun b => by
        refine (queryBound_restorePathsM _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        exact Nat.mul_le_mul_left _
          (by have := (modelParams M.toFieldModel sys.fri
                (starkShape sys M.extData.d pproof.active pproof.logDegrees)
                (M.wellFormed sys.fri _ htwo)).height_le b
              omega))
      (List.finRange _)).mono ?_
    rw [List.length_finRange]
  · refine (queryBound_mapM_oc
      (q := (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).queries *
        (3 * (modelParams M.toFieldModel sys.fri
          (starkShape sys M.extData.d pproof.active pproof.logDegrees)
          (M.wellFormed sys.fri _ htwo)).n + 1))
      (fun i => by
        refine (queryBound_restorePathsM _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        have hdim : Merkle.maxLogHeight ((modelParams M.toFieldModel sys.fri
            (starkShape sys M.extData.d pproof.active pproof.logDegrees)
            (M.wellFormed sys.fri _ htwo)).commitDims i).toList ≤
            (modelParams M.toFieldModel sys.fri
              (starkShape sys M.extData.d pproof.active pproof.logDegrees)
              (M.wellFormed sys.fri _ htwo)).n := by
          simp only [Compiled.Params.commitDims, List.toList_toArray, Merkle.maxLogHeight]
          omega
        exact Nat.mul_le_mul_left _ (by omega))
      (List.range _)).mono ?_
    rw [List.length_range]
  · split <;> exact queryBound_pure _ 0
  · simp only [Compiled.Params.verifierQueries]; ring_nf; omega

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_shardCompTensorPruned
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D) :
    (shardCompTensorPruned (fslots := fslots) (slots := slots) (width := width)
      M sys pproof m0 mid).QueryBound
      (shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) := by
  unfold shardCompTensorPruned
  split
  · next h =>
    dsimp only
    let P := modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) (M.wellFormed sys.fri _ h)
    have hrounds : P.rounds ≤ TwoAdicOps.twoAdicity (F := F) := P.rounds_le.trans h
    have hbatches : P.batches ≤ 4 := length_starkShape_leP sys M.extData.d pproof.active pproof.logDegrees
    have hvq : P.verifierQueries ≤
        (4 + TwoAdicOps.twoAdicity (F := F)) *
          (sys.fri.numQueries * (3 * TwoAdicOps.twoAdicity (F := F) + 1)) := by
      unfold Compiled.Params.verifierQueries
      exact Nat.mul_le_mul (Nat.add_le_add hbatches hrounds)
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 3 h) 1))
    refine QueryBound.mono
      (QueryBound.bind (m := P.verifierQueries + P.verifierQueries)
        (queryBound_deriveA _ _) fun t =>
          QueryBound.bind (m := P.verifierQueries)
            (queryBound_restoreShardPathsM M sys pproof h t) fun opt => ?_) ?_
    · cases opt with
      | none => exact queryBound_pure _ P.verifierQueries
      | some ps => exact Compiled.Params.queryBound_verifyWithTensor _ _ _ _ _ _ _ _ _
    · dsimp only [P] at hrounds hvq ⊢
      unfold shardQueriesPruned
      omega
  · exact queryBound_pure _ _

/-! ### Unpruning refinement for `checkAfterChallengesTensor` with `prunedMmcs` -/

omit [FieldOps EF] [ExtensionOps F EF] [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  [DecidableEq F] [DecidableEq EF] in
private lemma withPaths_friShapeOk (params : FriParams) (shape : ClaimShape)
    (commitments : Array D) (points values : Array EF)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (inPaths comPaths : Array (Array (List D))) :
    Fri.shapeOk (F := F) params shape commitments points values
        (pproof.withPaths inPaths comPaths).openingProof =
      Fri.shapeOk (F := F) params shape commitments points values pproof.openingProof := by
  have hall1 : (((pproof.withPaths inPaths comPaths).openingProof.commitPhaseOpenings).all
      (fun o => o.logArity == 1 && o.siblingValues.size == params.numQueries &&
        o.siblingValues.all fun s => s.size == 1)) =
      pproof.openingProof.commitPhaseOpenings.all (fun o => o.logArity == 1 &&
        o.siblingValues.size == params.numQueries && o.siblingValues.all fun s => s.size == 1) := by
    apply Bool.eq_iff_iff.mpr
    rw [Array.all_eq_true, Array.all_eq_true]
    simp only [Proof.withPaths, Array.size_mapIdx, Array.getElem_mapIdx]
  unfold Fri.shapeOk
  rw [hall1]
  simp only [Proof.withPaths, Array.size_mapIdx]
  apply congrArg (_ && ·)
  apply congrArg (List.all _)
  funext b
  rw [Array.getElem?_mapIdx]
  cases pproof.openingProof.inputOpenings[b]? <;> rfl

omit [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] in
private lemma withPaths_queryResultTensor (params : FriParams) (shape : ClaimShape)
    (points values : Array EF) (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (inPaths comPaths : Array (Array (List D))) (ch : TensorChallenges EF) (t : ℕ) :
    queryResultTensor (F := F) params shape points values
        (pproof.withPaths inPaths comPaths).openingProof ch t =
      queryResultTensor (F := F) params shape points values pproof.openingProof ch t := by
  have hqr : Fri.queryRows (pproof.withPaths inPaths comPaths).openingProof t =
      Fri.queryRows pproof.openingProof t := by
    unfold Fri.queryRows
    simp only [Proof.withPaths]
    apply Array.ext
    · simp
    · intro i hi1 hi2
      simp [Array.getElem_map, Array.getElem_mapIdx]
  have hsib : (fun i => Fri.sibling (pproof.withPaths inPaths comPaths).openingProof i t) =
      (fun i => Fri.sibling pproof.openingProof i t) := by
    funext i
    unfold Fri.sibling
    simp only [Proof.withPaths, Array.getElem?_mapIdx]
    cases pproof.openingProof.commitPhaseOpenings[i]? <;> rfl
  unfold queryResultTensor Fri.checkQueryTensor
  rw [hqr, hsib]
  rfl

private lemma mapM_id_eq_some_of_forall {α : Type*} (l : List (Option α)) (r : List α)
    (hlen : l.length = r.length)
    (h : ∀ i (hi : i < r.length), l[i]'(hlen ▸ hi) = some r[i]) :
    l.mapM id = some r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons a as ih =>
    cases r with
    | nil => cases hlen
    | cons b bs =>
      have h0 : a = some b := h 0 (Nat.zero_lt_succ _)
      subst h0
      have htail := ih bs (Nat.succ.inj hlen) fun i hi => h (i + 1) (Nat.succ_lt_succ hi)
      simp only [List.mapM_cons, id_eq, Option.bind_eq_bind, Option.bind_some, htail,
        Option.pure_def]

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private lemma withPaths_nextMsgTensor (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (m0 mid : RawMsg F EF D) (inPaths comPaths : Array (Array (List D))) :
    nextMsgTensor (fslots := fslots) (slots := slots) (width := width) M sys
        (pproof.withPaths inPaths comPaths) m0 mid =
      nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid := by
  funext i t
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        cases i with
        | zero => rfl
        | succ i =>
          cases i with
          | zero => rfl
          | succ j => rfl

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
private theorem unprune_verifyWithTensor_pruned
    (f : ∀ x, STAns F EF D K fslots slots width x)
    (params : FriParams) (shape : ClaimShape)
    (htwo : logMaxHeight params.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F))
    (coms : Array D) (pts vals : Array EF)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (ch : TensorChallenges EF)
    (msgM : ℕ → Compiled.Msg K D shape.length)
    (rT : PcsRbr.TensorChal K (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape))
    (βM : ℕ → K)
    (idxM : Fin (modelParams M.toFieldModel params shape (M.wellFormed params shape htwo)).queries → ℕ)
    (hfs : Fri.shapeOk (F := F) params shape coms pts vals pproof.openingProof = true)
    (hag0 : AgreesTensor M.toFieldModel params shape coms pts vals
      (pproof.withPaths #[] #[]).openingProof ch msgM rT βM idxM)
    (hw : verifyWithTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) params shape coms pts vals
      pproof.openingProof ch = true) :
    let P := modelParams M.toFieldModel params shape (M.wellFormed params shape htwo)
    let W := maxWidth shape
    let Mopen := maxOpeningsPerHeight params.logBlowup shape
    let p0 := pproof.withPaths #[] #[]
    ∃ (inPaths comPaths : Array (Array (List D))),
      ((List.finRange P.batches).map fun b =>
        restorePaths (hasherOf f) (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((modelProof M.toFieldModel params shape p0.openingProof).inputRows b))
          (match pproof.openingProof.inputOpenings[b.val]? with
            | some o => o.openingProof | none => ⟨#[]⟩)).mapM id = some inPaths.toList ∧
      ((List.range P.rounds).map fun i =>
        restorePaths (hasherOf f) (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> (i + 1))
          (Array.ofFn fun k : Fin P.queries =>
            #[#[(P.commitRowTensor W Mopen (tensorCoord params shape)
                  (modelProof M.toFieldModel params shape p0.openingProof) (msgM 0) rT βM
                  (idxM k) k i).1,
                (P.commitRowTensor W Mopen (tensorCoord params shape)
                  (modelProof M.toFieldModel params shape p0.openingProof) (msgM 0) rT βM
                  (idxM k) k i).2]])
          (match pproof.openingProof.commitPhaseOpenings[i]? with
            | some o => o.openingProof | none => ⟨#[]⟩)).mapM id = some comPaths.toList ∧
      verifyWithTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
        (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) params shape coms pts vals
        (pproof.withPaths inPaths comPaths).openingProof ch = true := by
  intro P W Mopen p0
  let comRow (i : ℕ) (k : Fin P.queries) : K × K :=
    P.commitRowTensor W Mopen (tensorCoord params shape)
      (modelProof M.toFieldModel params shape p0.openingProof) (msgM 0) rT βM (idxM k) k i
  have hfs0 : Fri.shapeOk (F := F) params shape coms pts vals p0.openingProof = true := by
    rw [withPaths_friShapeOk]; exact hfs
  have hw' : (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun k =>
        decide (ch.indices.getD k 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (prunedMmcs (inputHasher M.toFieldModel (hasherOf f))) params shape
        coms pproof.openingProof.inputOpenings ch.indices
      && (Array.ofFn fun k : Fin params.numQueries =>
        queryResultTensor (F := F) params shape pts vals pproof.openingProof ch k.val).all (·.ok)
      && commitChecks (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) params.numQueries
        (logMaxHeight params.logBlowup shape) (numRounds params shape)
        pproof.openingProof.commitPhaseCommits pproof.openingProof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          queryResultTensor (F := F) params shape pts vals pproof.openingProof ch k.val).map
          (·.rows))) = true := hw
  simp only [Bool.and_eq_true] at hw'
  obtain ⟨⟨⟨⟨⟨hpowB, hidxSzB⟩, hidxLtB⟩, hinPruned⟩, hqOk⟩, hcomPruned⟩ := hw'
  have hok_all : ∀ k : Fin params.numQueries,
      (queryResultTensor (F := F) params shape pts vals p0.openingProof ch k.val).ok = true :=
    fun k => by
      rw [withPaths_queryResultTensor]
      have := Array.all_eq_true.mp hqOk k.val (by rw [Array.size_ofFn]; exact k.isLt)
      simpa using this
  -- Step 1: Every input batch restores to `some paths` passing `Merkle.verifyOpenings`
  have hinEach : ∀ b : Fin P.batches,
      ∃ (root : D) (o : BatchOpening F (PrunedPaths D)) (paths : Array (List D)),
        coms[b.val]? = some root ∧
        pproof.openingProof.inputOpenings[b.val]? = some o ∧
        restorePaths (hasherOf f) (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((modelProof M.toFieldModel params shape p0.openingProof).inputRows b))
          o.openingProof = some paths ∧
        Merkle.verifyOpenings (inputHasher M.toFieldModel (hasherOf f)) root
          (batchDims params.logBlowup (shape.getD b.val []))
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>>
              (logMaxHeight params.logBlowup shape -
                Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b.val [])).toList))
          o.openedValues paths = true := by
    intro b
    simp only [Fri.inputChecks, List.all_eq_true, List.mem_range] at hinPruned
    have hb := hinPruned b.val b.isLt
    split at hb
    · next root o hroot ho =>
      obtain ⟨paths, hrest, hver⟩ := prunedMmcs_accepts hb
      obtain ⟨hrowsSz, _⟩ := Exec.Checks.size_of_verifyOpenings hver
      rw [Array.size_ofFn] at hrowsSz
      have ho' : pproof.openingProof.inputOpenings[b.val]? =
          some (o : BatchOpening F (PrunedPaths D)) := ho
      have ho0 : p0.openingProof.inputOpenings[b.val]? =
          some { openedValues := o.openedValues, openingProof := #[] } := by
        dsimp only [p0, Proof.withPaths]
        rw [Array.getElem?_mapIdx, ho']; rfl
      have hrowsEq : Array.ofFn
            ((modelProof M.toFieldModel params shape p0.openingProof).inputRows b) =
          o.openedValues.map fun r => r.map fun row => row.map M.base.toModel :=
        Exec.Checks.ofFn_inputRows M.toFieldModel params shape b ho0 hrowsSz
      have hidx_eq : (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) =
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>>
              (logMaxHeight params.logBlowup shape -
                Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b.val [])).toList)) := by
        congr 1; funext k; rw [hag0.index k]; rfl
      have hrestM : restorePaths (hasherOf f) (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((modelProof M.toFieldModel params shape p0.openingProof).inputRows b))
          o.openingProof = some paths := by
        rw [hrowsEq, hidx_eq]
        exact (restorePaths_map M.base.toModel (hasherOf f) (P.dims b) _ o.openedValues
          o.openingProof).symm.trans hrest
      exact ⟨root, o, paths, hroot, ho, hrestM, hver⟩
    · exact absurd hb (by simp)
  -- Step 2: Every folding round restores to `some paths` passing `Merkle.verifyOpenings`
  have hcomEach : ∀ i : ℕ, i < P.rounds →
      ∃ (root : D) (o : CommitPhaseStep EF (PrunedPaths D)) (paths : Array (List D)),
        pproof.openingProof.commitPhaseCommits[i]? = some root ∧
        pproof.openingProof.commitPhaseOpenings[i]? = some o ∧
        restorePaths (hasherOf f) (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> (i + 1))
          (Array.ofFn fun k : Fin P.queries => #[#[(comRow i k).1, (comRow i k).2]])
          o.openingProof = some paths ∧
        Merkle.verifyOpenings (friHasher M.toFieldModel (hasherOf f)) root #[⟨2, P.n - i - 1⟩]
          (Array.ofFn (n := params.numQueries) fun k => ch.indices.getD k.val 0 >>> (i + 1))
          (Array.ofFn (n := params.numQueries) fun k =>
            #[#[((queryResultTensor (F := F) params shape pts vals pproof.openingProof ch k.val).rows.getD i
                  (0, 0)).1,
                ((queryResultTensor (F := F) params shape pts vals pproof.openingProof ch k.val).rows.getD i
                  (0, 0)).2]])
          paths = true := by
    intro i hi
    simp only [Fri.commitChecks, List.all_eq_true, List.mem_range] at hcomPruned
    have hci := hcomPruned i hi
    split at hci
    · next root o hroot ho =>
      obtain ⟨paths, hrest, hver⟩ := prunedMmcs_accepts hci
      have hrowsEq :
          (Array.ofFn (n := P.queries) fun k =>
            #[#[((queryResultTensor (F := F) params shape pts vals pproof.openingProof ch k.val).rows.getD i
                  (0, 0)).1,
                ((queryResultTensor (F := F) params shape pts vals pproof.openingProof ch k.val).rows.getD i
                  (0, 0)).2]]).map
            (fun r => r.map fun row => row.map M.ext.toModel) =
          Array.ofFn fun k : Fin P.queries => #[#[(comRow i k).1, (comRow i k).2]] := by
        rw [Exec.Checks.map_ofFn_pair]
        congr 1; funext k
        have hqr := rows_queryResultTensor M.toFieldModel params shape (M.wellFormed params shape htwo)
          hfs0 hag0 k (hok_all k) hi
        rw [withPaths_queryResultTensor] at hqr
        exact congrArg (fun p : K × K => #[#[p.1, p.2]]) hqr
      have hidx_eq : (Array.ofFn fun k : Fin P.queries => idxM k >>> (i + 1)) =
          (Array.ofFn (n := params.numQueries) fun k => ch.indices.getD k.val 0 >>> (i + 1)) := by
        congr 1; funext k; rw [hag0.index k]
      have hrestM : restorePaths (hasherOf f) (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> (i + 1))
          (Array.ofFn fun k : Fin P.queries => #[#[(comRow i k).1, (comRow i k).2]])
          o.openingProof = some paths := by
        rw [← hrowsEq, hidx_eq]
        simp only [Exec.Checks.getD_map_ofFn] at hrest
        exact (restorePaths_map M.ext.toModel (hasherOf f) (P.commitDims i) _ _
          o.openingProof).symm.trans hrest
      simp only [Exec.Checks.getD_map_ofFn] at hver
      exact ⟨root, o, paths, hroot, ho, hrestM, hver⟩
    · exact absurd hci (by simp)
  -- Assemble the restored unpruned path arrays deterministically (no `Classical.choose`)
  let inOpt (b : Fin P.batches) : Option (Array (List D)) :=
    restorePaths (hasherOf f) (P.dims b)
      (Array.ofFn fun k : Fin P.queries =>
        idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
      (Array.ofFn ((modelProof M.toFieldModel params shape p0.openingProof).inputRows b))
      (match pproof.openingProof.inputOpenings[b.val]? with
        | some o => o.openingProof | none => ⟨#[]⟩)
  let comOpt (i : ℕ) : Option (Array (List D)) :=
    restorePaths (hasherOf f) (P.commitDims i)
      (Array.ofFn fun k : Fin P.queries => idxM k >>> (i + 1))
      (Array.ofFn fun k : Fin P.queries => #[#[(comRow i k).1, (comRow i k).2]])
      (match pproof.openingProof.commitPhaseOpenings[i]? with
        | some o => o.openingProof | none => ⟨#[]⟩)
  let inPaths : Array (Array (List D)) := Array.ofFn fun b : Fin P.batches => (inOpt b).getD #[]
  let comPaths : Array (Array (List D)) := Array.ofFn fun i : Fin P.rounds => (comOpt i.val).getD #[]
  refine ⟨inPaths, comPaths, ?_, ?_, ?_⟩
  · refine mapM_id_eq_some_of_forall _ inPaths.toList (by simp [inPaths]) fun i hi => ?_
    have hi' : i < P.batches := by simpa [inPaths] using hi
    obtain ⟨root, o, paths, -, ho, hrestM, -⟩ := hinEach ⟨i, hi'⟩
    have hopt : inOpt ⟨i, hi'⟩ = some paths := by
      dsimp only [inOpt]; rw [ho]; exact hrestM
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Array.getElem_toList, inPaths,
      Array.getElem_ofFn, hopt, Option.getD_some]
    exact hopt
  · refine mapM_id_eq_some_of_forall _ comPaths.toList (by simp [comPaths]) fun i hi => ?_
    have hi' : i < P.rounds := by simpa [comPaths] using hi
    obtain ⟨root, o, paths, -, ho, hrestM, -⟩ := hcomEach i hi'
    have hopt : comOpt i = some paths := by
      dsimp only [comOpt]; rw [ho]; exact hrestM
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, comPaths,
      Array.getElem_ofFn, hopt, Option.getD_some]
    exact hopt
  · have hinUnpruned : inputChecks (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))) params
        shape coms (pproof.withPaths inPaths comPaths).openingProof.inputOpenings ch.indices = true := by
      refine Exec.CompletenessChecks.inputChecks_of_open
        (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))) fun b hb => ?_
      have hb' : b < P.batches := hb
      obtain ⟨root, o, paths, hroot, ho, hrestM, hver⟩ := hinEach ⟨b, hb'⟩
      have hopt : inOpt ⟨b, hb'⟩ = some paths := by
        dsimp only [inOpt]; rw [ho]; exact hrestM
      have hget : inPaths.getD b #[] = paths := by
        simp [inPaths, Array.getD_eq_getD_getElem?, hb', hopt]
      refine ⟨root, { openedValues := o.openedValues, openingProof := paths }, hroot, ?_, hver⟩
      exact ((Array.getElem?_mapIdx ..).trans (congrArg (Option.map _) ho)).trans
        (congrArg (fun p => some (BatchOpening.mk o.openedValues p)) hget)
    have hcomUnpruned : commitChecks (merkleMmcs (friHasher M.toFieldModel (hasherOf f)))
        params.numQueries (logMaxHeight params.logBlowup shape) (numRounds params shape)
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseCommits
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          queryResultTensor (F := F) params shape pts vals
            (pproof.withPaths inPaths comPaths).openingProof ch k.val).map (·.rows)) = true := by
      refine Exec.CompletenessChecks.commitChecks_of_open
        (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) fun i hi => ?_
      have hi' : i < P.rounds := hi
      obtain ⟨root, o, paths, hroot, ho, hrestM, hver⟩ := hcomEach i hi'
      have hopt : comOpt i = some paths := by
        dsimp only [comOpt]; rw [ho]; exact hrestM
      have hget : comPaths.getD i #[] = paths := by
        simp [comPaths, Array.getD_eq_getD_getElem?, hi', hopt]
      refine ⟨root, { logArity := o.logArity, siblingValues := o.siblingValues, openingProof := paths },
        hroot, ?_, ?_⟩
      · exact ((Array.getElem?_mapIdx ..).trans (congrArg (Option.map _) ho)).trans
          (congrArg (fun p => some (CommitPhaseStep.mk o.logArity o.siblingValues p)) hget)
      · simp only [merkleMmcs, Exec.Checks.getD_map_ofFn, withPaths_queryResultTensor]
        exact hver
    show (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun k =>
        decide (ch.indices.getD k 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))) params shape coms
        (pproof.withPaths inPaths comPaths).openingProof.inputOpenings ch.indices
      && (Array.ofFn fun k : Fin params.numQueries =>
        queryResultTensor (F := F) params shape pts vals
          (pproof.withPaths inPaths comPaths).openingProof ch k.val).all (·.ok)
      && commitChecks (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) params.numQueries
        (logMaxHeight params.logBlowup shape) (numRounds params shape)
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseCommits
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          queryResultTensor (F := F) params shape pts vals
            (pproof.withPaths inPaths comPaths).openingProof ch k.val).map (·.rows))) = true
    have hqOk' : (Array.ofFn fun k : Fin params.numQueries =>
        queryResultTensor (F := F) params shape pts vals
          (pproof.withPaths inPaths comPaths).openingProof ch k.val).all (·.ok) = true := by
      simp only [withPaths_queryResultTensor]; exact hqOk
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨hpowB, hidxSzB⟩, hidxLtB⟩, hinUnpruned⟩, hqOk'⟩, hcomUnpruned⟩

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
/-- **Core pruned-to-unpruned bridge for one tensor STARK shard:**
If `checkAfterChallengesTensor` with `prunedMmcs` accepts `pproof` against oracle `f`,
then `restoreShardPathsM` succeeds against `f` with restored path arrays `(inPaths, comPaths)`
such that `checkAfterChallengesTensor` with unpruned `merkleMmcs` accepts
`pproof.withPaths inPaths comPaths` against `f`. -/
theorem unprune_of_checkAfterChallengesTensor_pruned
    (f : ∀ x, STAns F EF D K fslots slots width x)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D)
    (hshape : Stark.shapeOk sys pproof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid j
      (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) j)) s 2
      (.ext γ :: mid) false 0 0)
    (hcheck : checkAfterChallengesTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      pproof s β γ acc = true) :
    ∃ (htwo : logMaxHeight sys.fri.logBlowup
        (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
          TwoAdicOps.twoAdicity (F := F))
      (inPaths comPaths : Array (Array (List D))),
      (restoreShardPathsM M sys pproof htwo
        (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid)
          (4 + ((modelParams M.toFieldModel sys.fri
            (starkShape sys M.extData.d pproof.active pproof.logDegrees)
            (M.wellFormed sys.fri _ htwo)).rounds + 2)))).run f =
          some (inPaths, comPaths) ∧
      checkAfterChallengesTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
        (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
        sys (pproof.withPaths inPaths comPaths) s β γ acc = true := by
  set next := nextMsgTensor (fslots := fslots) (slots := slots) (width := width)
    M sys (pproof.withPaths #[] #[]) m0 mid
  set ms := fun j => next j (fsTranscriptA f next j)
  set shape := starkShape sys M.extData.d pproof.active pproof.logDegrees
  set ζ := Function.surjInv M.surj (answer f ms 3).field
  have hlast : ∀ j, tLastField (fsTranscriptA f next (j + 1)) = (answer f ms j).field := fun j => by
    show UTensorAns.field (f (.chal (fsTranscriptA f next j) (next j (fsTranscriptA f next j)))) =
      UTensorAns.field (f (.chal (fsTranscript f ms j) (next j (fsTranscriptA f next j))))
    rw [← fsTranscriptA_eq_fsTranscript]
  have hsh : claimShape (openingClaims
      (InputProof := (prunedMmcs (inputHasher M.toFieldModel (hasherOf f))).MultiProof)
      (CommitProof := (prunedMmcs (friHasher M.toFieldModel (hasherOf f))).MultiProof)
      sys pproof ζ) = shape := by
    change claimShape (openingClaims sys pproof ζ) = shape
    rw [claimShape_openingClaims sys pproof hshape ζ, ← M.degree_eq]
  have h2 : ms 2 = (.ext γ :: mid) ++ secondMessage pproof := by
    show Observation.ext (rep M (tLastField (fsTranscriptA f next 2))) ::
      (mid ++ secondMessage pproof) = _
    rw [hlast 1, hγ]; rfl
  have h4 : ms 4 = (claimValues (openingClaims sys pproof ζ)).toList.map .ext := by
    show List.map Observation.ext (claimValues (openingClaims sys pproof
      (rep M (tLastField (fsTranscriptA f next 4))))).toList = _
    rw [hlast 3]; rfl
  have hC : ∀ i < numRounds sys.fri shape,
      ms (5 + i) = .digest (pproof.openingProof.commitPhaseCommits.getD i default) ::
        (if sys.fri.commitPowBits = 0 then []
          else [.base (pproof.openingProof.commitPowWitnesses.getD i 0)]) := fun i hi => by
    rw [Nat.add_comm 5 i]
    show messages sys.fri shape #[] #[] #[] (pproof.withPaths #[] #[]).openingProof (i + 1) = _
    rw [messages, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi),
      Nat.add_sub_cancel]
    rfl
  have hF : ms (5 + numRounds sys.fri shape) =
      finalMessage (numRounds sys.fri shape) pproof.openingProof.finalPoly ++
        (if sys.fri.queryPowBits = 0 then [] else [.base pproof.openingProof.queryPowWitness]) := by
    rw [Nat.add_comm 5 (numRounds sys.fri shape)]
    show messages sys.fri shape #[] #[] #[] (pproof.withPaths #[] #[]).openingProof
      (numRounds sys.fri shape + 1) = _
    rw [messages, ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Nat.not_succ_le_self _)]
    rfl
  obtain ⟨hz, hc, hu, hfs, ch, hch, hw, hcol, hopen, hcolW, hopenW, hβ, hpow, hidx⟩ :=
    checkAfterChallengesTensor_ufreeTensor M f
      (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f)))
      sys pproof hshape β γ acc hs h2 rfl h4 (by rw [hsh]; exact hC) (by rw [hsh]; exact hF)
      hcheck
  rw [hsh] at hfs hch hw hcol hopen hcolW hopenW hβ hpow hidx
  have htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F) := by
    have h := hfs
    simp only [Fri.shapeOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.1.1.1.1.1.1.2
  set P := modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri shape htwo)
  set W := maxWidth shape
  set Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
  set t := fsTranscriptA f next (4 + (P.rounds + 2))
  have hlen_ch : ∀ {n : ℕ}
      (tr : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width) n),
      (chalsOf tr).length = n := by
    intro n tr
    induction tr with
    | nil => rfl
    | snoc _ _ _ ih =>
      show (chalsOf _ ++ [_]).length = _
      rw [List.length_append, ih, List.length_singleton]
  have hch_at : ∀ n (k : ℕ), k < n →
      tAnsAt (chalsOf (fsTranscript f ms n)) k = answer f ms k := by
    intro n
    induction n with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ n ih =>
      intro k hk
      show ((chalsOf (fsTranscript f ms n) ++ [answer f ms n])[k]?).getD _ = answer f ms k
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | hEq
      · rw [List.getElem?_append_left (by rw [hlen_ch]; exact hlt)]
        exact ih k hlt
      · subst hEq
        have heq := List.getElem?_concat_length (l := chalsOf (fsTranscript f ms k))
          (a := answer f ms k)
        rw [hlen_ch] at heq
        rw [heq]; rfl
  have hans : ∀ j < 4 + (P.rounds + 2), tAnsAt (chalsOf t) j = answer f ms j := fun j hj => by
    rw [show t = fsTranscript f ms (4 + (P.rounds + 2)) from fsTranscriptA_eq_fsTranscript f next _]
    exact hch_at _ j hj
  have hζ_eq : rep M (tFieldAt (chalsOf t) 3) = ζ := by
    show rep M (tAnsAt (chalsOf t) 3).field = _
    rw [hans 3 (by omega)]; rfl
  have hcolSz : ch.schedule.colChallenges.size = tensorNumChallenges W := by
    rw [hcol, List.size_toArray, List.length_map, List.length_range]
  have hopenSz : ch.schedule.openChallenges.size = tensorNumChallenges Mopen := by
    rw [hopen, List.size_toArray, List.length_map, List.length_range]
  set rT := tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4)
  set βM : ℕ → K := fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0
  set idxM : Fin P.queries → ℕ := fun k => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
    (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n
  set ζt := rep M (tFieldAt (chalsOf t) 3)
  set coms := (openingClaims sys pproof ζt).map (·.commitment)
  set pts := claimPoints (openingClaims sys pproof ζt)
  set vals := claimValues (openingClaims sys pproof ζt)
  set msgM : ℕ → Compiled.Msg K D shape.length :=
    fun j => view M.toFieldModel sys.fri shape (messages sys.fri shape coms pts vals pproof.openingProof j)
  have hfs_t : Fri.shapeOk (F := F) sys.fri shape coms pts vals pproof.openingProof = true := by
    dsimp only [coms, pts, vals]; rw [hζ_eq]; exact hfs
  have hw_t : verifyWithTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) sys.fri shape coms pts vals
      pproof.openingProof ch = true := by
    dsimp only [coms, pts, vals]; rw [hζ_eq]; exact hw
  have hag0 : AgreesTensor M.toFieldModel sys.fri shape coms pts vals
      (pproof.withPaths #[] #[]).openingProof ch msgM rT βM idxM :=
    { msg := fun _ _ => rfl
      colSize := hcolSz
      openSize := hopenSz
      colWeights := hcolW
      openWeights := hopenW
      colChals := fun b => by
        dsimp only [rT, tensorChalOfAns]
        rw [hans 4 (by omega)]
        have hlt : b.val < ch.schedule.colChallenges.size := by rw [hcolSz]; exact b.isLt
        have hg : ch.schedule.colChallenges[b.val]'hlt =
            Function.surjInv M.surj ((answer f ms 4).fieldAt b.val) := by
          have := Transcript.getD_map_range (fun k =>
            Function.surjInv M.surj ((answer f ms 4).fieldAt k)) (tensorNumChallenges W) b.val 0
          rw [ite_eq_left b.isLt] at this
          rw [← this, ← hcol, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hg, Function.surjInv_eq M.surj]
      openChals := fun b => by
        dsimp only [rT, tensorChalOfAns]
        rw [hans 4 (by omega)]
        have hlt : b.val < ch.schedule.openChallenges.size := by rw [hopenSz]; exact b.isLt
        have hg : ch.schedule.openChallenges[b.val]'hlt =
            Function.surjInv M.surj ((answer f ms 4).fieldAt (tensorNumChallenges W + b.val)) := by
          have := Transcript.getD_map_range (fun k =>
            Function.surjInv M.surj ((answer f ms 4).fieldAt (tensorNumChallenges W + k)))
            (tensorNumChallenges Mopen) b.val 0
          rw [ite_eq_left b.isLt] at this
          rw [← this, ← hopen, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hg, Function.surjInv_eq M.surj]
      beta := fun i hi => by
        dsimp only [βM]
        have hi' : i < P.rounds := hi
        rw [ite_eq_left hi', tFieldAt, hans (5 + i) (by omega), hβ, Transcript.getD_map_range,
          ite_eq_left hi, Function.surjInv_eq M.surj]
      index := fun k => by
        dsimp only [idxM]
        rw [hans (5 + P.rounds) (by omega), hidx, Transcript.getD_map_range, ite_eq_left k.isLt]
        rfl }
  obtain ⟨inPaths, comPaths, hinMapM, hcomMapM, hwithUnpruned⟩ :=
    unprune_verifyWithTensor_pruned M f sys.fri shape htwo coms pts vals pproof ch msgM rT βM idxM
      hfs_t hag0 hw_t
  refine ⟨htwo, inPaths, comPaths, ?_, ?_⟩
  · -- Show `(restoreShardPathsM ...).run f = some (inPaths, comPaths)`
    unfold restoreShardPathsM
    simp only [run_bind, run_mapM_oc, run_restorePathsM]
    rw [hinMapM, hcomMapM]
    simp
  · -- Reassemble `checkAfterChallengesTensor` directly (identical challenges `α, ζ, ch`!)
    have hα_s : (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).alpha =
        Function.surjInv M.surj (answer f ms 2).field := by
      have a2 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage pproof))
          2 (ms 2) false 0 0 := by
        rw [h2]; exact hs.observeAll f M.toFieldModel _
      exact (a2.sampleExt_zero f M.toFieldModel).1
    have hζ_s : (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = ζ := by
      have a2 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage pproof))
          2 (ms 2) false 0 0 := by
        rw [h2]; exact hs.observeAll f M.toFieldModel _
      obtain ⟨-, a2'⟩ := a2.sampleExt_zero f M.toFieldModel
      have a3 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observe
          ((uChallengerTensor f M.toFieldModel).sampleExt
            ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage pproof))).2
          (.digest pproof.quotientCommit)) 3 (ms 3) false 0 0 := a2'.observe_next f M.toFieldModel _
      exact (a3.sampleExt_zero f M.toFieldModel).1
    have hζ_st : (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = ζt :=
      hζ_s.trans hζ_eq.symm
    have hsh_t : claimShape (openingClaims sys pproof ζt) = shape := by
      rw [hζ_eq]; exact hsh
    have hch_eq : transcriptFromTensor (uChallengerTensor f M.toFieldModel)
        (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).state sys.fri shape vals
        (pproof.withPaths inPaths comPaths).openingProof = ch := by
      dsimp only [vals]; rw [hζ_eq]; exact hch.symm
    simp only [checkAfterChallengesTensor, verifyClaimsFromTensor,
      verifyFromTensor, Bool.and_eq_true]
    change (zetaOk pproof (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = true ∧
        widthsUniform (openingClaims sys pproof
          (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta) = true ∧
        Fri.shapeOk sys.fri
          (claimShape (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          ((openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta).map (·.commitment))
          (claimPoints (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (claimValues (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (pproof.withPaths inPaths comPaths).openingProof = true ∧
        verifyWithTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
          (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys.fri
          (claimShape (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          ((openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta).map (·.commitment))
          (claimPoints (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (claimValues (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (pproof.withPaths inPaths comPaths).openingProof
          (transcriptFromTensor (uChallengerTensor f M.toFieldModel)
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).state sys.fri
            (claimShape (openingClaims sys pproof
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
            (claimValues (openingClaims sys pproof
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
            (pproof.withPaths inPaths comPaths).openingProof) = true) ∧
      constraintsOk sys pproof β γ acc
        (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).alpha
        (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = true
    rw [hα_s, hζ_st]
    refine ⟨⟨by rw [hζ_eq]; exact hz, by rw [hζ_eq]; exact hu, ?_, ?_⟩, by rw [hζ_eq]; exact hc⟩
    · rw [hsh_t, withPaths_friShapeOk]; exact hfs_t
    · suffices ∀ sh : ClaimShape, sh = shape →
          verifyWithTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
            (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys.fri sh coms pts vals
            (pproof.withPaths inPaths comPaths).openingProof
            (transcriptFromTensor (uChallengerTensor f M.toFieldModel)
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).state sys.fri sh vals
              (pproof.withPaths inPaths comPaths).openingProof) = true from
        this _ hsh_t
      rintro sh rfl
      rw [hch_eq]
      exact hwithUnpruned

/-- **Deterministic pruned-shard soundness in a good log.** -/
theorem shard_goodTensorPruned (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys V θ B r l) {f : ∀ x, STAns F EF D K fslots slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    {l₀ l₁ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensorPruned M sys pproof m0 mid) l₀ b l₁) (hl₁ : l₁ <+: l)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid 2
      (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = pproof.active) (hstage1 : hdr.stage1Commit = pproof.stage1Commit)
    (hlogs : hdr.logDegrees = pproof.logDegrees)
    (hdig : pproof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hshape : Stark.shapeOk sys pproof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid j
      (fsTranscriptA f (nextMsgTensor M sys (pproof.withPaths #[] #[]) m0 mid) j)) s 2
      (.ext γ :: mid) false 0 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallengesTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      pproof s β γ acc = true) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) pproof.active pproof.logDegrees
        pproof.stage1Commit pproof.stage2Commit pproof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (pproof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  obtain ⟨htwo, inPaths, comPaths, hrunRest, hcheckUnpruned⟩ :=
    unprune_of_checkAfterChallengesTensor_pruned M sys f pproof m0 mid hshape β γ acc s hγ hs hcheck
  unfold shardCompTensorPruned at hout
  rw [dite_eq_left htwo, outcome_bind] at hout
  obtain ⟨t, l', hder, hrest_bind⟩ := hout
  obtain ⟨opt, l'', hrest, hver⟩ := outcome_bind.mp hrest_bind
  have hfl₁ : ∀ x y, l₁.dlookup x = some y → f x = y := fun x y h =>
    hf x y (dlookup_of_prefix h hl₁)
  have hfl'' : ∀ x y, l''.dlookup x = some y → f x = y := fun x y h =>
    hfl₁ x y (dlookup_of_prefix h hver.prefix)
  have hfl' : ∀ x y, l'.dlookup x = some y → f x = y := fun x y h =>
    hfl'' x y (dlookup_of_prefix h hrest.prefix)
  obtain rfl := hder.eq_fsTranscriptA hfl'
  have hopt : opt = some (inPaths, comPaths) := (hrest.run_eq hfl'').symm.trans hrunRest
  subst hopt
  dsimp only at hver
  set proof := pproof.withPaths inPaths comPaths
  have hnextEq := withPaths_nextMsgTensor (fslots := fslots) (slots := slots) (width := width)
    M sys pproof m0 mid inPaths comPaths
  rw [← hnextEq] at hder hhdr hβ hγ hs
  exact shard_goodTensor_of_derive_verify M sys V θ B r hfixed hheightOk hθ hgood hf proof m0 mid
    hmid htwo hder hrest.prefix hver hl₁ hdec hpre hhdr hactive hstage1 hlogs hdig hdigFixed hr
    hshape β γ acc s hβ hγ hs hacc hcheckUnpruned

/-! ## 4. Single-Shard & Batch Pruned Tensor STARK Soundness -/

section PrunedSingle

variable (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyTensor` with `CertiFri.P3.prunedMmcs` against an oracle `f`.** -/
noncomputable def verifyTensorPrunedAccepts (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : SAttemptPruned F EF D) : Bool :=
  Stark.verifyTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a.claims a.proof

/-- Lookup challenges of a pruned single-shard tensor STARK run against `f`. -/
noncomputable def lookupOfTensorPruned (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : SAttemptPruned F EF D) : EF × EF :=
  ((lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims))).1,
    (lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims))).2.1)

/-- Constraint violation event for a pruned single-shard attempt. -/
def ViolatesTensorPruned (l : Log (STAns F EF D K fslots slots width))
    (f : ∀ x, STAns F EF D K fslots slots width x) (a : SAttemptPruned F EF D) : Prop :=
  ConstraintFail M sys θ (M.baseRows (committedRow l)) a.proof.active a.proof.logDegrees
    a.proof.stage1Commit a.proof.stage2Commit a.proof.quotientCommit
    (M.ext.toModel (lookupOfTensorPruned M sys f a).1)
    (M.ext.toModel (lookupOfTensorPruned M sys f a).2)
    (M.ext.toModel (claimsAccumulator (lookupOfTensorPruned M sys f a).1
      (lookupOfTensorPruned M sys f a).2 a.claims).2)
    (a.proof.intermediateAccumulators.map M.ext.toModel)

/-- Lookup balance predicate for a pruned single-shard attempt. -/
def LookupsBalancedTensorPruned (l : Log (STAns F EF D K fslots slots width))
    (a : SAttemptPruned F EF D) : Prop :=
  Balanced (allItems M sys θ
    (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2) a.preamble)

/-- Soundness experiment for `Stark.verifyTensor` with `prunedMmcs`. -/
noncomputable def experimentTensorStarkPruned {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → SAttemptPruned F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardCompTensorPruned M sys (attempt a).proof
      (firstMessage sys (attempt a).proof (attempt a).claims) []).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_experimentTensorStarkPruned {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttemptPruned F EF D) :
    (experimentTensorStarkPruned M sys adv attempt).QueryBound
      (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    (queryBound_shardCompTensorPruned M sys _ _ _).bind fun _ => queryBound_pure _ 0

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem headerOk_of_shapeOkP {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (hshape : Stark.shapeOk sys proof = true)
    {claims : Array (Array F)} (hclaims : claims.size ≤ B.claims)
    (hlen : ∀ c ∈ claims, c.size ≤ B.len) :
    HeaderOk sys B ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩ := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, -⟩, hlogs⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hact⟩ := hshape
  refine ⟨hsize, hlogs, fun pos => ?_, hclaims, hlen⟩
  show proof.logDegrees.getD pos 0 ≤ sys.maxLogDegree
  by_cases hpos : pos < (activeIndices proof.active).length
  · have hmem : ((activeIndices proof.active)[pos], pos) ∈ (activeIndices proof.active).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      exact List.getElem?_eq_getElem hpos
    exact (hact _ hmem).1.1.1.1.1.1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    exact Nat.zero_le _

theorem verifyTensorPruned_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys (singleVariant sys B) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : SAttemptPruned F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensorPruned M sys a.proof (firstMessage sys a.proof a.claims) [])
      l₀ b l)
    (hacc : verifyTensorPrunedAccepts M sys f a = true) (hcov : CoveredPruned B a) :
    ¬ ViolatesTensorPruned M sys θ l f a ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩)).eval
            (Polynomial.C (M.ext.toModel (lookupOfTensorPruned M sys f a).1))).eval
          (M.ext.toModel (lookupOfTensorPruned M sys f a).2) ≠ 0) := by
  simp only [verifyTensorPrunedAccepts, Stark.verifyTensor, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, -⟩, -, hcheck⟩ := hacc
  have hhdr := headerOk_of_shapeOkP sys B hshape hcov.claims hcov.claim_len
  have hdec : (singleVariant (EF := EF) sys B).dec0 (firstMessage sys a.proof a.claims) =
      some ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ := by
    rw [firstMessage_eq]
    exact singleVariant_dec0 M.base hN hcast hhdr
  have hpre : PreOk sys B
      ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ :=
    ⟨hshards, fun h hh => by rwa [List.mem_singleton.mp (Array.mem_toList_iff.mpr hh)],
      Nat.zero_le _, fun m hm => absurd hm (Array.not_mem_empty m)⟩
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards a.proof a.claims
  have a0 : UAtTensor (fun j => nextMsgTensor M sys (a.proof.withPaths #[] #[])
        (firstMessage sys a.proof a.claims) [] j
        (fsTranscriptA f (nextMsgTensor M sys (a.proof.withPaths #[] #[])
          (firstMessage sys a.proof a.claims) []) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims)) 0 (firstMessage sys a.proof a.claims) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (firstMessage sys a.proof a.claims)
    (ms := fun j => nextMsgTensor M sys (a.proof.withPaths #[] #[])
      (firstMessage sys a.proof a.claims) [] j
      (fsTranscriptA f (nextMsgTensor M sys (a.proof.withPaths #[] #[])
        (firstMessage sys a.proof a.claims) []) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  exact shard_goodTensorPruned M sys (singleVariant sys B) θ B (maxRounds F) hfixed hheightOk hθ
    hgood hf a.proof (firstMessage sys a.proof a.claims) [] (fun o ho => absurd ho List.not_mem_nil)
    hout (List.prefix_refl l) hdec hpre
    (hdr := ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩) rfl rfl rfl rfl
    (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self)
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs rfl hcheck

/-- **Unconditional unique-decoding soundness of `Stark.verifyTensor` with `prunedMmcs`.** -/
theorem soundness_verifyTensorPruned_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorPrunedAccepts M sys f (attempt out.1) = true ∧
          CoveredPruned B (attempt out.1) ∧
          ViolatesTensorPruned M sys (1 - δ) l f (attempt out.1))
      (experimentTensorStarkPruned M sys adv attempt) [] ≤
      (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := singleVariant sys B) (θ := 1 - δ)
      (B := B) (r := maxRounds F) (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots
      hcommit hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_experimentTensorStarkPruned M sys hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hviol⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyTensorPruned_good M sys (1 - δ) B hfixed hheightOk hshards hN hcast (by linarith)
    hgood hf (attempt a) hcomp hacc hcov).1 hviol

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyTensor` with `prunedMmcs`.** -/
theorem soundness_verifyTensorPruned_lookups_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorPrunedAccepts M sys f (attempt out.1) = true ∧
          CoveredPruned B (attempt out.1) ∧
          ¬ LookupsBalancedTensorPruned M sys (1 - δ) B l (attempt out.1))
      (experimentTensorStarkPruned M sys adv attempt) [] ≤
      (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := singleVariant sys B) (θ := 1 - δ)
      (B := B) (r := maxRounds F) (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots
      hcommit hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_experimentTensorStarkPruned M sys hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  obtain ⟨hviol, hbal⟩ := verifyTensorPruned_good M sys (1 - δ) B hfixed hheightOk hshards hN hcast
    (by linarith) hgood hf (attempt a) hcomp hacc hcov
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  simp only [verifyTensorPrunedAccepts, Stark.verifyTensor, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, hres⟩, hclaims, -⟩ := hacc
  have hitems : allItems M sys (1 - δ)
      (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
        (committedRow l)).2)
      ⟨#[⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
        (attempt a).claims⟩], #[]⟩ =
      headerItems M sys (1 - δ)
        (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
          (committedRow l)).2)
        ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
          (attempt a).claims⟩ := by
    rw [allItems]; exact (List.append_nil _).trans (List.flatMap_singleton _ _)
  rw [hitems] at hne hsum
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards (attempt a).proof (attempt a).claims
  have hlast := toModel_residualT M sys (1 - δ) (com := M.baseRows (committedRow l))
    (hdr := ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit,
      (attempt a).proof.logDegrees, (attempt a).claims⟩)
    (β := (lookupOfTensorPruned M sys f (attempt a)).1)
    (γ := (lookupOfTensorPruned M sys f (attempt a)).2)
    hplain h2 hshape rfl rfl rfl
    (baseRows_readMsgT M B _ (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self))
    (fun root hroot => baseRows_readMsgT M B _
      (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
    htwo hclaims hviol hne
  exact hsum (hlast.symm.trans (((M.ext.beq_iff _ _).mp hres).trans M.ext.map_zero))

end PrunedSingle

section PrunedBatch

variable (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyBatchTensor` with `CertiFri.P3.prunedMmcs` against an oracle `f`.** -/
noncomputable def batchTensorPrunedAccepts (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : BAttemptPruned F EF D) : Bool :=
  Stark.verifyBatchTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a

/-- Shared lookup challenges of a pruned batch tensor STARK run against `f`. -/
noncomputable def batchLookupOfTensorPruned (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : BAttemptPruned F EF D) : EF × EF :=
  ((lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble))).1,
    (lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble))).2.1)

/-- Constraint violation event for a pruned batch attempt. -/
def BatchViolatesTensorPruned (l : Log (STAns F EF D K fslots slots width))
    (f : ∀ x, STAns F EF D K fslots slots width x) (a : BAttemptPruned F EF D) : Prop :=
  ∃ (i : ℕ) (hdr : ShardHeader F D) (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)),
    a.preamble.headers[i]? = some hdr ∧ a.proofs[i]? = some proof ∧
    ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
      proof.stage1Commit proof.stage2Commit proof.quotientCommit
      (M.ext.toModel (batchLookupOfTensorPruned M sys f a).1)
      (M.ext.toModel (batchLookupOfTensorPruned M sys f a).2)
      (M.ext.toModel (claimsAccumulator (batchLookupOfTensorPruned M sys f a).1
        (batchLookupOfTensorPruned M sys f a).2 hdr.claims).2)
      (proof.intermediateAccumulators.map M.ext.toModel)

/-- Lookup balance predicate for a pruned batch attempt. -/
def BatchLookupsBalancedTensorPruned (l : Log (STAns F EF D K fslots slots width))
    (a : BAttemptPruned F EF D) : Prop :=
  Balanced (allItems M sys θ
    (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
      (committedRow l)).2) a.preamble)

/-- Sequential verification of pruned tensor shards. -/
noncomputable def shardsCompTensorPruned (m0 : RawMsg F EF D) :
    List (Proof F EF D (PrunedPaths D) (PrunedPaths D)) → ℕ →
      OracleComp (STAns F EF D K fslots slots width) Bool
  | [], _ => .pure true
  | proof :: rest, i =>
    (shardCompTensorPruned M sys proof m0 [observeNat i]).bind fun b =>
      (shardsCompTensorPruned m0 rest (i + 1)).bind fun b' => .pure (b && b')

/-- Soundness experiment for `Stark.verifyBatchTensor` with `prunedMmcs`. -/
noncomputable def batchExperimentTensorStarkPruned {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → BAttemptPruned F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardsCompTensorPruned M sys (batchFirstMessage sys (attempt a).preamble)
      ((attempt a).proofs.toList.take B.shards) 0).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
private theorem queryBound_shardsCompTensorPruned (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (PrunedPaths D) (PrunedPaths D))) (i : ℕ) :
    (shardsCompTensorPruned (fslots := fslots) (slots := slots) (width := width)
      M sys m0 proofs i).QueryBound
      (proofs.length * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) := by
  induction proofs generalizing i with
  | nil => exact queryBound_pure _ _
  | cons proof rest ih =>
    have h : (shardsCompTensorPruned (fslots := fslots) (slots := slots) (width := width)
        M sys m0 (proof :: rest) i).QueryBound
        (shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) +
          (rest.length * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) + 0)) :=
      (queryBound_shardCompTensorPruned M sys proof m0 _).bind fun _ =>
        (ih (i + 1)).bind fun _ => queryBound_pure _ _
    exact h.mono (by rw [List.length_cons, Nat.succ_mul]; omega)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_batchExperimentTensorStarkPruned {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned F EF D) :
    (batchExperimentTensorStarkPruned M sys B adv attempt).QueryBound
      (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    ((queryBound_shardsCompTensorPruned M sys _ _ 0).mono
      (Nat.mul_le_mul_right _ (List.length_take_le _ _))).bind fun _ => queryBound_pure _ 0

private theorem outcome_shardsCompTensorPruned (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (PrunedPaths D) (PrunedPaths D))) (i₀ : ℕ)
    {l l' : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (h : Outcome (shardsCompTensorPruned M sys m0 proofs i₀) l b l') (k : ℕ)
    {proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)} (hk : proofs[k]? = some proof) :
    ∃ (l₀ : Log (STAns F EF D K fslots slots width)) (b' : Bool)
      (l₁ : Log (STAns F EF D K fslots slots width)),
      Outcome (shardCompTensorPruned M sys proof m0 [observeNat (i₀ + k)]) l₀ b' l₁ ∧ l₁ <+: l' := by
  induction proofs generalizing i₀ l b k with
  | nil => exact absurd hk (by simp)
  | cons p rest ih =>
    rw [shardsCompTensorPruned] at h
    obtain ⟨b₁, l₁, h₁, h⟩ := outcome_bind.mp h
    obtain ⟨b₂, l₂, h₂, h₃⟩ := outcome_bind.mp h
    obtain ⟨-, rfl⟩ := h₃
    cases k with
    | zero =>
      obtain rfl : p = proof := by simpa using hk
      exact ⟨l, b₁, l₁, h₁, h₂.prefix⟩
    | succ k =>
      obtain ⟨l₀, b', l₁', h', hp⟩ := ih (i₀ + 1) h₂ k (by simpa using hk)
      have e : i₀ + 1 + k = i₀ + (k + 1) := by omega
      rw [e] at h'
      exact ⟨l₀, b', l₁', h', hp⟩

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem headerOk_of_shardOkP {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (hshape : Stark.shapeOk sys proof = true)
    {hdr : ShardHeader F D} (hactive : hdr.active = proof.active)
    (hlogs : hdr.logDegrees = proof.logDegrees) (hclaims : hdr.claims.size ≤ B.claims)
    (hlen : ∀ c ∈ hdr.claims, c.size ≤ B.len) : HeaderOk sys B hdr := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, -⟩, hlogs'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hact⟩ := hshape
  refine ⟨by rw [hactive]; exact hsize, by rw [hlogs, hactive]; exact hlogs', fun pos => ?_,
    hclaims, hlen⟩
  rw [hlogs]
  by_cases hpos : pos < (activeIndices proof.active).length
  · have hmem : ((activeIndices proof.active)[pos], pos) ∈ (activeIndices proof.active).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      exact List.getElem?_eq_getElem hpos
    exact (hact _ hmem).1.1.1.1.1.1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    exact Nat.zero_le _

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
theorem shardOkTensor_of_batchTensorPrunedAccepts {f : ∀ x, STAns F EF D K fslots slots width x}
    {a : BAttemptPruned F EF D} (hacc : batchTensorPrunedAccepts M sys f a = true) :
    a.preamble.headers.size = a.proofs.size ∧
      ∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        Stark.shapeOk sys proof = true ∧ hdr.active = proof.active ∧
          hdr.stage1Commit = proof.stage1Commit ∧ hdr.logDegrees = proof.logDegrees ∧
          checkAfterChallengesTensor (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
            (prunedMmcs (friHasher M.toFieldModel (hasherOf f)))
            (uChallengerTensor f M.toFieldModel) sys proof
            ((uChallengerTensor f M.toFieldModel).observe
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).2.2 (observeNat i))
            (lookupChallenges (uChallengerTensor f M.toFieldModel)
              ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                (batchFirstMessage sys a.preamble))).1
            (lookupChallenges (uChallengerTensor f M.toFieldModel)
              ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                (batchFirstMessage sys a.preamble))).2.1
            (claimsAccumulator
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).1
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).2.1 hdr.claims).2 = true := by
  simp only [batchTensorPrunedAccepts, Stark.verifyBatchTensor, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hacc
  obtain ⟨⟨-, hsz⟩, ⟨-, hall⟩, -⟩ := hacc
  refine ⟨hsz, fun i hdr proof hhdr hproof => ?_⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOkTensor, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, -, hcheck⟩ := h
  exact ⟨hshape, hactive, hstage1, hlogs, hcheck⟩

theorem verifyBatchTensorPruned_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttemptPruned F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardsCompTensorPruned M sys (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchTensorPrunedAccepts M sys f a = true) (hcov : BatchCoveredPruned B a) {i : ℕ}
    {hdr : ShardHeader F D} {proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)}
    (hhdr : a.preamble.headers[i]? = some hdr) (hproof : a.proofs[i]? = some proof) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit
        (M.ext.toModel (batchLookupOfTensorPruned M sys f a).1)
        (M.ext.toModel (batchLookupOfTensorPruned M sys f a).2)
        (M.ext.toModel (claimsAccumulator (batchLookupOfTensorPruned M sys f a).1
          (batchLookupOfTensorPruned M sys f a).2 hdr.claims).2)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble)).eval
            (Polynomial.C (M.ext.toModel (batchLookupOfTensorPruned M sys f a).1))).eval
          (M.ext.toModel (batchLookupOfTensorPruned M sys f a).2) ≠ 0) := by
  obtain ⟨hsz, hall⟩ := shardOkTensor_of_batchTensorPrunedAccepts M sys hacc
  obtain ⟨hshape, hactive, hstage1, hlogs, hcheck⟩ := hall i hdr proof hhdr hproof
  have hmem : hdr ∈ a.preamble.headers := Array.mem_of_getElem? hhdr
  have hi : i < B.shards :=
    lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hhdr).1 hcov.shards
  have hpre : PreOk sys B a.preamble := by
    refine ⟨hcov.shards, fun h hh => ?_, hcov.messages, hcov.message_len⟩
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp hh
    have hklt : k < a.proofs.size := hsz ▸ (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨hshape', hactive', -, hlogs', -⟩ :=
      hall k h a.proofs[k] hk (Array.getElem?_eq_getElem hklt)
    exact headerOk_of_shardOkP sys B hshape' hactive' hlogs' (hcov.claims h hh).1
      (hcov.claims h hh).2
  have hdec := batchVariant_dec0 (EF := EF) M.base hN hcast hpre
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  have hk : (a.proofs.toList.take B.shards)[i]? = some proof := by
    rw [List.getElem?_take_of_lt hi, Array.getElem?_toList]; exact hproof
  obtain ⟨l₀', b', l₁, hcomp, hl₁⟩ := outcome_shardsCompTensorPruned M sys _ _ 0 hout i hk
  rw [Nat.zero_add] at hcomp
  have a0 : UAtTensor (fun j => nextMsgTensor M sys (proof.withPaths #[] #[])
        (batchFirstMessage sys a.preamble) [observeNat i] j
        (fsTranscriptA f (nextMsgTensor M sys (proof.withPaths #[] #[])
          (batchFirstMessage sys a.preamble) [observeNat i]) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble)) 0 (batchFirstMessage sys a.preamble) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (batchFirstMessage sys a.preamble)
    (ms := fun j => nextMsgTensor M sys (proof.withPaths #[] #[])
      (batchFirstMessage sys a.preamble) [observeNat i] j
      (fsTranscriptA f (nextMsgTensor M sys (proof.withPaths #[] #[])
        (batchFirstMessage sys a.preamble) [observeNat i]) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  have hs' := hs.observe f M.toFieldModel (observeNat i)
  have hshard : (batchVariant (EF := EF) sys B N).shard
      (nextMsgTensor M sys (proof.withPaths #[] #[]) (batchFirstMessage sys a.preamble)
        [observeNat i] 2
        (fsTranscriptA f (nextMsgTensor M sys (proof.withPaths #[] #[])
          (batchFirstMessage sys a.preamble) [observeNat i]) 2)) = i :=
    batchVariant_shard M.base sys B hcast _ (hi.le.trans hN.shards) _
  exact shard_goodTensorPruned M sys (batchVariant sys B N) θ B (maxRounds F) hfixed hheightOk hθ
    hgood hf proof (batchFirstMessage sys a.preamble) [observeNat i]
    (fun o ho => ⟨_, List.mem_singleton.mp ho⟩) hcomp hl₁ hdec hpre (hdr := hdr)
    (by rw [hshard]; exact hhdr) hactive hstage1 hlogs
    (by
      rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩))
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs' rfl hcheck

/-- **Unconditional unique-decoding soundness of `Stark.verifyBatchTensor` with `prunedMmcs`.** -/
theorem soundness_verifyBatchTensorPruned_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorPrunedAccepts M sys f (attempt out.1) = true ∧
          BatchCoveredPruned B (attempt out.1) ∧
          BatchViolatesTensorPruned M sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorStarkPruned M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := batchVariant sys B N) (θ := 1 - δ)
      (B := B) (r := maxRounds F) (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots
      hcommit hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_batchExperimentTensorStarkPruned M sys B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, i, hdr, proof, hhdr, hproof, hfail⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyBatchTensorPruned_good M sys (1 - δ) B hfixed hheightOk hN hcast (by linarith)
    hgood hf (attempt a) hcomp hacc hcov hhdr hproof).1 hfail

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
private theorem sums_of_batchTensorPrunedAccepts {f : ∀ x, STAns F EF D K fslots slots width x}
    {a : BAttemptPruned F EF D} (hacc : batchTensorPrunedAccepts M sys f a = true) :
    a.preamble.headers.size ≠ 0 ∧
      (messagesAccumulator (batchLookupOfTensorPruned M sys f a).1
        (batchLookupOfTensorPruned M sys f a).2
        (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).1 = true ∧
      (∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        (claimsAccumulator (batchLookupOfTensorPruned M sys f a).1
          (batchLookupOfTensorPruned M sys f a).2 hdr.claims).1 = true) ∧
      (a.proofs.foldl (fun total proof => total + Stark.residual proof)
        (messagesAccumulator (batchLookupOfTensorPruned M sys f a).1
          (batchLookupOfTensorPruned M sys f a).2
          (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2 == 0) = true := by
  simp only [batchTensorPrunedAccepts, Stark.verifyBatchTensor, Bool.and_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq] at hacc
  obtain ⟨⟨hne, -⟩, ⟨hmsgs, hall⟩, hzero⟩ := hacc
  refine ⟨hne, hmsgs, fun i hdr proof hhdr hproof => ?_, hzero⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOkTensor, Bool.and_eq_true] at h
  exact h.2.1

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyBatchTensor` with
`prunedMmcs`.** -/
theorem soundness_verifyBatchTensorPruned_lookups_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorPrunedAccepts M sys f (attempt out.1) = true ∧
          BatchCoveredPruned B (attempt out.1) ∧
          ¬ BatchLookupsBalancedTensorPruned M sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorStarkPruned M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := batchVariant sys B N) (θ := 1 - δ)
      (B := B) (r := maxRounds F) (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots
      hcommit hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_batchExperimentTensorStarkPruned M sys B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  obtain ⟨hsz, hall⟩ := shardOkTensor_of_batchTensorPrunedAccepts M sys hacc
  obtain ⟨hne0, hmsgs, hclaims, hzero⟩ := sums_of_batchTensorPrunedAccepts M sys hacc
  have hshardGood := fun {i : ℕ} {hdr : ShardHeader F D}
      {proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)}
      (hhdr : (attempt a).preamble.headers[i]? = some hdr)
      (hproof : (attempt a).proofs[i]? = some proof) =>
    verifyBatchTensorPruned_good M sys (1 - δ) B hfixed hheightOk hN hcast (by linarith) hgood hf
      (attempt a) hcomp hacc hcov hhdr hproof
  have h0' : 0 < (attempt a).preamble.headers.size := Nat.pos_of_ne_zero hne0
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero
    ((hshardGood (Array.getElem?_eq_getElem h0') (Array.getElem?_eq_getElem (hsz ▸ h0'))).2 hnb)
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  have hshard : ∀ (i : ℕ) (hdr : ShardHeader F D)
      (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)),
      (attempt a).preamble.headers.toList[i]? = some hdr →
      (attempt a).proofs.toList[i]? = some proof →
      M.ext.toModel (Stark.residual proof) =
        lookupSum (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).1)
          (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).2)
          (headerItems M sys (1 - δ)
            (M.baseRows (readMsg B (batchFirstMessage sys (attempt a).preamble : RawMsg F EF D)
              (committedRow l)).2) hdr) := by
    intro i hdr proof hhdr hproof
    rw [Array.getElem?_toList] at hhdr hproof
    obtain ⟨hshape, hactive, hstage1, hlogs, -⟩ := hall i hdr proof hhdr hproof
    have hmem : hdr ∈ (attempt a).preamble.headers := Array.mem_of_getElem? hhdr
    refine toModel_residualT M sys (1 - δ) (com := M.baseRows (committedRow l)) hplain h2 hshape
      hactive hstage1 hlogs (baseRows_readMsgT M B _ ?_)
      (fun root hroot => baseRows_readMsgT M B _ ?_)
      htwo (hclaims i hdr proof hhdr hproof) (hshardGood hhdr hproof).1 fun it hit => hne it ?_
    · rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩)
    · rw [hdigs, hroot]
      exact List.mem_append_left _ List.mem_cons_self
    · rw [allItems]
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, hit⟩)
  have hm : M.ext.toModel (messagesAccumulator (batchLookupOfTensorPruned M sys f (attempt a)).1
      (batchLookupOfTensorPruned M sys f (attempt a)).2
      ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2 =
      lookupSum (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).1)
        (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).2)
        ((attempt a).preamble.messages.toList.map fun m =>
          (M.base.toModel m.multiplicity, m.args.toList.map M.base.toModel)) :=
    (messagesAccumulator_model M _ _ _ hmsgs).2.trans (congrArg _ List.map_map)
  have hfold := toModel_foldl_residualT M _ _ (headerItems M sys (1 - δ) _)
    (attempt a).preamble.headers.toList (attempt a).proofs.toList
    (by rw [Array.length_toList, Array.length_toList, hsz]) hshard
    (messagesAccumulator (batchLookupOfTensorPruned M sys f (attempt a)).1
      (batchLookupOfTensorPruned M sys f (attempt a)).2
      ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2
  refine hsum ?_
  rw [allItems, lookupSum_append, add_comm, ← hm, ← hfold, Array.foldl_toList]
  exact ((M.ext.beq_iff _ _).mp hzero).trans M.ext.map_zero

end PrunedBatch

end PrunedStark

end CertiFri.Exec.Stark
