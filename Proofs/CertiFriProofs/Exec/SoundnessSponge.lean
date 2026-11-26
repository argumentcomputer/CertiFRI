import CertiFriProofs.Exec.SoundnessUnconditional
import CertiFriProofs.Exec.SoundnessJohnson
import CertiFriProofs.P3.DigestCard
import CertiFriProofs.Theory.Oracle.SpongeCommitted
import CertiFriProofs.Theory.ProximityGap.CurveListCA

/-!
# Incremental sponge FRI soundness (`c = 3 / 2`) & RFC 7693 `BLAKE2b-512` theorems

This module lifts the compiled and executable FRI soundness theorems from
full-transcript Fiat–Shamir (`entryCap = batches + rounds`, collision prefactor
`c = (batches + rounds + 3) / 4 ≈ 7.75`) to incremental sponge chaining
(`entryCap = 1`, collision prefactor **`c = 3 / 2`**) using
`Oracle.prob_spongeExperiment_bind_committedRow_le` (`Theory/Oracle/SpongeCommitted.lean`).

Each input commitment root is absorbed individually (steps `0 .. batches - 1`,
`1` digest each, `0` error), followed by the opening points and claimed values
(step `batches`, `0` digests, squeezing `α`), each folding commitment root
(steps `batches + 1 .. batches + rounds`, `1` digest each, squeezing `β_i`),
and the final polynomial (step `batches + rounds + 1`, `0` digests, squeezing
queries). Every single sponge step brings at most **`1`** digest into play
(`entryCap = 1`) for arbitrary `batches` and `rounds`, giving the exact
collision bound **`3 * N ^ 2 / (2 * Fintype.card D)`**.

## Concrete theorems proved (zero `sorry`, core Lean + Mathlib axioms only)

* `Exec.soundness_sponge`: general executable `Fri.verify` soundness under
  incremental sponge chaining (`c = 3 / 2`) for arbitrary `CurveMCA` + `StepMCA`.
* `Exec.soundness_sponge_uniqueDecoding`: unconditional unique-decoding
  soundness (`c = 3 / 2`).
* `Exec.soundness_sponge_johnson`: Johnson-regime soundness (`c = 3 / 2`) under
  `CurveListCA`.
* `CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_uniqueDecoding`:
  production 128-bit **classical** 32-byte `BLAKE3-256` (`Digest`, `|D| = 2 ^ 256`)
  incremental sponge bound `N * εmax + 3 * N ^ 2 / (2 * 2 ^ 256)` (`127.71`-bit
  classical BCS collision bound, improving over `126.52` bits with zero prover cost).
* `CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding`:
  64-byte RFC 7693 `BLAKE2b-512` (`Digest64`, `|D| = 2 ^ 512`, 512-bit internal
  state) instantiation in the **classical** random oracle model, giving
  `N * εmax + 3 * N ^ 2 / (2 * 2 ^ 512)` (`255.71`-bit classical BCS collision
  bound, so the classical collision term stays `≤ N / (4 * 2 ^ 128)` up to
  `N ≤ 2 ^ 128`). Note: this proves **classical ROM** soundness,
  not 128-bit post-quantum soundness — QROM Fiat–Shamir and Grover search
  against FRI queries/PoW are not formalized here.
  *(Replaces legacy `BLAKE3-XOF48`/`BLAKE3-XOF64`, whose 256-bit internal `cv`
  limits generic hash-output cardinality.)*
* `CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128`:
  literal `≤ N / 2 ^ 128` soundness even at `N = 2 ^ 128` for unconditional UD
  parameters `(logBlowup = 2, numQueries = 160, commitPowBits = 0, queryPowBits = 20)`
  over `GoldilocksExt3` with `BLAKE2b-512`.
* `CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_128` and
  `goldilocksExt3_soundness_sponge_blake2b512_johnson_*_128_unconditional`:
  literal `≤ N / 2 ^ 128` Johnson-regime soundness (`lb = 2, 3, 4`) over
  `GoldilocksExt3` with `BLAKE2b-512` (`Digest64`).
-/

namespace CertiFri.Sponge

open Oracle OracleComp MerkleRO Compiled
open PcsRbr (Chal GrindChal ClaimsFail Accepts PowPasses ungrind roundError)

/-! ## Lifting hash-only oracle computations (`verifyWith`) to sponge oracles -/

section MapHash

variable {M : Type} {C : ℕ → Type} {T D : Type}

/-- Answer type of a pure hash oracle (no challenge queries, since `Msg = Empty`). -/
abbrev HashOnlyAnswer (T D : Type) :=
  MerkleAnswer Empty (fun _ : ℕ => PUnit) T D

/-- Lift a hash-only computation into a sponge-Merkle computation. -/
def mapHashToSponge {α : Type*} :
    OracleComp (HashOnlyAnswer T D) α → OracleComp (SpongeMerkleAnswer M C T D) α
  | .pure a => .pure a
  | .queryBind (.chal _ m) _ => Empty.elim m
  | .queryBind (.other q) k => .queryBind (.other q) fun y => mapHashToSponge (k y)

/-- Project a sponge-Merkle log to its hash entries as a hash-only log. -/
def projHashLog (l : Log (SpongeMerkleAnswer M C T D)) : Log (HashOnlyAnswer T D) :=
  l.filterMap fun
    | ⟨.chal _ _ _, _⟩ => none
    | ⟨.other q, y⟩ => some ⟨.other q, y⟩

/-- Project a sponge-Merkle oracle function to a hash-only oracle function. -/
def projHashFun (f : ∀ x : SpongeQuery M D (HashQuery T D), SpongeMerkleAnswer M C T D x) :
    ∀ x : FSQuery Empty (fun _ : ℕ => PUnit) (HashQuery T D), HashOnlyAnswer T D x
  | .chal _ m => Empty.elim m
  | .other q => f (.other q)

theorem projHashLog_append (l₁ l₂ : Log (SpongeMerkleAnswer M C T D)) :
    projHashLog (l₁ ++ l₂) = projHashLog l₁ ++ projHashLog l₂ := by
  simp [projHashLog, List.filterMap_append]

theorem projHashLog_dlookup [DecidableEq T] [DecidableEq D]
    [DecidableEq (SpongeQuery M D (HashQuery T D))]
    (l : Log (SpongeMerkleAnswer M C T D)) (q : HashQuery T D) :
    (projHashLog l).dlookup (.other q) = l.dlookup (.other q) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rcases e with ⟨x, y⟩
    cases x with
    | chal i prev m =>
      rw [projHashLog, List.filterMap_cons]
      dsimp only
      rw [List.dlookup_cons_ne _ _ (by simp)]
      exact ih
    | other q' =>
      rw [projHashLog, List.filterMap_cons]
      dsimp only
      by_cases hq : q' = q
      · subst hq
        simp only [List.dlookup, ↓reduceDIte]
        rfl
      · have hne1 : FSQuery.other q ≠ (⟨FSQuery.other q', y⟩ : Sigma (HashOnlyAnswer T D)).fst :=
          fun h => hq (FSQuery.other.inj h).symm
        have hne2 : SpongeQuery.other q ≠
            (⟨SpongeQuery.other q', y⟩ : Sigma (SpongeMerkleAnswer M C T D)).fst :=
          fun h => hq (SpongeQuery.other.inj h).symm
        rw [List.dlookup_cons_ne _ _ hne1, List.dlookup_cons_ne _ _ hne2]
        exact ih

theorem queryBound_mapHashToSponge {α : Type*} :
    ∀ {c : OracleComp (HashOnlyAnswer T D) α} {Q : ℕ},
      c.QueryBound Q → (mapHashToSponge (M := M) (C := C) c).QueryBound Q
  | .pure _, _, _ => trivial
  | .queryBind (.chal _ m) _, _, _ => Empty.elim m
  | .queryBind (.other _) _, 0, hc => absurd hc (queryBound_queryBind_zero _ _)
  | .queryBind (.other _) _, _ + 1, hc => fun y => queryBound_mapHashToSponge (hc y)

theorem run_mapHashToSponge {α : Type*}
    (f : ∀ x : SpongeQuery M D (HashQuery T D), SpongeMerkleAnswer M C T D x) :
    ∀ (c : OracleComp (HashOnlyAnswer T D) α),
      (mapHashToSponge c).run f = c.run (projHashFun f)
  | .pure _ => rfl
  | .queryBind (.chal _ m) _ => Empty.elim m
  | .queryBind (.other q) k => run_mapHashToSponge f (k (f (.other q)))

theorem outcome_projHashLog [DecidableEq T] [DecidableEq D]
    [DecidableEq (SpongeQuery M D (HashQuery T D))] {α : Type*} :
    ∀ {c : OracleComp (HashOnlyAnswer T D) α}
      {l l' : Log (SpongeMerkleAnswer M C T D)} {a : α},
      Outcome (mapHashToSponge c) l a l' → Outcome c (projHashLog l) a (projHashLog l')
  | .pure _, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := outcome_pure.mp h
    exact outcome_pure.mpr ⟨rfl, rfl⟩
  | .queryBind (.chal _ m) _, _, _, _, _ => Empty.elim m
  | .queryBind (.other q) k, l, l', a, h => by
    cases hlook : l.dlookup (.other q) with
    | some y =>
      rw [mapHashToSponge, outcome_queryBind_of_lookup hlook] at h
      rw [outcome_queryBind_of_lookup ((projHashLog_dlookup l q).trans hlook)]
      exact outcome_projHashLog h
    | none =>
      rw [mapHashToSponge, outcome_queryBind_of_fresh hlook] at h
      obtain ⟨y, hy⟩ := h
      rw [outcome_queryBind_of_fresh ((projHashLog_dlookup l q).trans hlook)]
      refine ⟨y, ?_⟩
      have hsub := outcome_projHashLog hy
      rwa [projHashLog_append] at hsub

theorem logCollision_projHashLog_iff {l : Log (SpongeMerkleAnswer M C T D)} :
    LogCollision hashObs (projHashLog l) ↔ LogCollision spongeHashObs l := by
  constructor
  · rintro ⟨⟨x₁, y₁⟩, h₁, ⟨x₂, y₂⟩, h₂, hne, z, hz₁, hz₂⟩
    simp only [projHashLog, List.mem_filterMap] at h₁ h₂
    obtain ⟨⟨x₁', y₁'⟩, hm₁, he₁⟩ := h₁
    obtain ⟨⟨x₂', y₂'⟩, hm₂, he₂⟩ := h₂
    cases x₁' with
    | chal _ _ _ => cases he₁
    | other q₁ =>
      cases x₂' with
      | chal _ _ _ => cases he₂
      | other q₂ =>
        injection he₁ with he₁
        injection he₂ with he₂
        have hq₁ : x₁ = .other q₁ := congrArg Sigma.fst he₁.symm
        have hq₂ : x₂ = .other q₂ := congrArg Sigma.fst he₂.symm
        subst hq₁; subst hq₂
        have hy₁ : y₁ = y₁' := eq_of_heq (Sigma.mk.inj he₁.symm).2
        have hy₂ : y₂ = y₂' := eq_of_heq (Sigma.mk.inj he₂.symm).2
        subst hy₁; subst hy₂
        exact ⟨⟨.other q₁, y₁⟩, hm₁, ⟨.other q₂, y₂⟩, hm₂,
          fun h => hne (congrArg FSQuery.other (SpongeQuery.other.inj h)), z, hz₁, hz₂⟩
  · rintro ⟨⟨x₁, y₁⟩, h₁, ⟨x₂, y₂⟩, h₂, hne, z, hz₁, hz₂⟩
    cases x₁ with
    | chal _ _ _ => cases hz₁
    | other q₁ =>
      cases x₂ with
      | chal _ _ _ => cases hz₂
      | other q₂ =>
        refine ⟨⟨.other q₁, y₁⟩, List.mem_filterMap.mpr ⟨⟨.other q₁, y₁⟩, h₁, rfl⟩,
          ⟨.other q₂, y₂⟩, List.mem_filterMap.mpr ⟨⟨.other q₂, y₂⟩, h₂, rfl⟩,
          fun h => hne (congrArg SpongeQuery.other (FSQuery.other.inj h)), z, hz₁, hz₂⟩

theorem committedRow_projHashLog [DecidableEq T] [DecidableEq D]
    [DecidableEq (SpongeQuery M D (HashQuery T D))]
    (l : Log (SpongeMerkleAnswer M C T D)) :
    committedRow (projHashLog l) = spongeCommittedRow l := by
  have hhasher : logHasher (projHashLog l) = spongeLogHasher l := by
    unfold logHasher spongeLogHasher
    have hlookup : ∀ q, hashLookup (projHashLog l) q = spongeHashLookup l q :=
      fun q => projHashLog_dlookup l q
    congr 1
    · funext xs; rw [hlookup]
    · funext a b; cases a <;> cases b <;> simp [hlookup]
  have hopens : ∀ root dims index rows,
      Opens (projHashLog l) root dims index rows ↔ SpongeOpens l root dims index rows := by
    intro root dims index rows
    unfold Opens SpongeOpens
    rw [hhasher]
  have hshows : ∀ root dims m i,
      ShowsRow (projHashLog l) root dims m i = SpongeShowsRow l root dims m i := by
    intro root dims m i
    funext r
    exact propext (by unfold ShowsRow SpongeShowsRow; simp only [hopens])
  funext root dims m i
  unfold committedRow spongeCommittedRow
  rw [hshows root dims m i]

end MapHash

/-! ## Single-root incremental absorption lift for `Compiled.Params` (`entryCap = 1`) -/

section CompiledSponge

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

/-- Challenge type of the `(P.batches + P.rounds + 2)`-step incremental sponge
protocol: steps `0 .. P.batches - 1` absorb one input batch root each (`PUnit`),
and steps `P.batches + k` carry round `k`'s `GrindChal`. -/
def SpongeChal (P : Params F) (bits : ℕ → ℕ) (i : ℕ) : Type :=
  if i < P.batches then PUnit else GrindChal bits (Chal P.ldt P.queries) (i - P.batches)

instance (P : Params F) (bits : ℕ → ℕ) (i : ℕ) : Fintype (SpongeChal P bits i) := by
  unfold SpongeChal
  split_ifs
  · exact inferInstanceAs (Fintype PUnit)
  · exact inferInstanceAs (Fintype (GrindChal bits (Chal P.ldt P.queries) (i - P.batches)))

instance (P : Params F) (bits : ℕ → ℕ) (i : ℕ) : Nonempty (SpongeChal P bits i) := by
  have : ∀ k, Nonempty (Chal P.ldt P.queries k) :=
    PcsRbr.Chal.nonempty P.domain_zero_nonempty P.queries
  unfold SpongeChal
  split_ifs
  · exact ⟨()⟩
  · exact inferInstanceAs (Nonempty (GrindChal bits (Chal P.ldt P.queries) (i - P.batches)))

omit [Fintype F] in
private theorem spongeChal_add_eq (P : Params F) (bits : ℕ → ℕ) (k : ℕ) :
    SpongeChal P bits (P.batches + k) = GrindChal bits (Chal P.ldt P.queries) k := by
  unfold SpongeChal
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- Cast a sponge challenge at step `P.batches + k` to round `k`'s `GrindChal`. -/
def spongeChalCast (P : Params F) (bits : ℕ → ℕ) {k : ℕ}
    (c : SpongeChal P bits (P.batches + k)) : GrindChal bits (Chal P.ldt P.queries) k :=
  cast (spongeChal_add_eq P bits k) c

/-- Inverse cast: round `k`'s `GrindChal` as a sponge challenge at step `P.batches + k`. -/
def spongeChalOf (P : Params F) (bits : ℕ → ℕ) {k : ℕ}
    (c : GrindChal bits (Chal P.ldt P.queries) k) : SpongeChal P bits (P.batches + k) :=
  cast (spongeChal_add_eq P bits k).symm c

omit [Fintype F] in
theorem spongeChalCast_of (P : Params F) (bits : ℕ → ℕ) {k : ℕ}
    (c : GrindChal bits (Chal P.ldt P.queries) k) :
    spongeChalCast P bits (spongeChalOf P bits c) = c := by
  simp [spongeChalCast, spongeChalOf]

omit [Fintype F] in
theorem spongeChalOf_cast (P : Params F) (bits : ℕ → ℕ) {k : ℕ}
    (c : SpongeChal P bits (P.batches + k)) :
    spongeChalOf P bits (spongeChalCast P bits c) = c := by
  simp [spongeChalCast, spongeChalOf]

/-- Interpreted message of one step of the single-root incremental sponge protocol:
* `.batchRoot fn`: the committed rows of one input batch root (steps `< P.batches`);
* `.round0Meta pts vals`: the opening points and claimed values (step `P.batches`, 0 roots);
* `.pcs m`: a `PcsRbr` message for a folding round or final polynomial (steps `> P.batches`). -/
inductive StepMsg (F : Type) (numClaims : ℕ → ℕ) : Type
  | batchRoot (fn : Array Dimensions → ℕ → ℕ → Option (Array F))
  | round0Meta (points values : List (List F))
  | pcs (m : PcsRbr.Msg F numClaims)

/-- Assemble `PcsRbr.Msg` of round `0` from the `P.batches` per-batch row
functions absorbed in steps `0 .. P.batches - 1` together with the opening
points and claimed values of step `P.batches`. -/
noncomputable def assembleClaims (P : Params F)
    (batchFns : Fin P.batches → Array Dimensions → ℕ → ℕ → Option (Array F))
    (points values : List (List F)) : PcsRbr.Msg F P.numClaims where
  claims j k :=
    { f := ofIndexed (2 ^ (P.n - j)) (fun i => P.shift * pointOfIndex P.ω P.n (P.n - j) i) fun i =>
        entry (batchFns (P.slot j k).batch (P.dims (P.slot j k).batch) (P.slot j k).matrix i)
          (P.slot j k).col
      z := (points.getD j []).getD k.val 0
      y := (values.getD j []).getD k.val 0 }
  word := fun _ => 0

omit [Fintype F] [Fintype D] [Nonempty D] [DecidableEq D] in
/-- `assembleClaims` equals `P.read 0 msg c` when `batchFns b = c (msg.inputRoots b)`. -/
theorem assembleClaims_eq_read_zero (P : Params F) (msg : Msg F D P.batches)
    (c : D → Array Dimensions → ℕ → ℕ → Option (Array F)) :
    P.read 0 msg c =
      assembleClaims P (fun b => c (msg.inputRoots b)) msg.points msg.values := rfl

/-- Extract the batch-`b` committed-row function from a `StepMsg` transcript. -/
def extractBatchFn (P : Params F) {C : ℕ → Type} {i : ℕ}
    (t : Transcript (StepMsg F P.numClaims) C i) (b : Fin P.batches) :
    Array Dimensions → ℕ → ℕ → Option (Array F) :=
  match t.msgs[b.val]? with
  | some (.batchRoot fn) => fn
  | _ => fun _ _ _ => none

/-- Extract the `PcsRbr.Msg` of step `P.batches + k` from `StepMsg` and the
previously absorbed batch functions. -/
noncomputable def extractStepPcsMsg (P : Params F)
    (batchFns : Fin P.batches → Array Dimensions → ℕ → ℕ → Option (Array F))
    (k : ℕ) (m : StepMsg F P.numClaims) : PcsRbr.Msg F P.numClaims :=
  match k, m with
  | 0, .round0Meta pts vals => assembleClaims P batchFns pts vals
  | _, .pcs pm => pm
  | _, _ => ⟨fun _ _ => ⟨fun _ => 0, 0, 0⟩, fun _ => 0⟩

/-- Extract the `k`-round `PcsRbr` transcript from a `(P.batches + k)`-step
incremental sponge transcript of `StepMsg`s. -/
noncomputable def extractPcs (P : Params F) (bits : ℕ → ℕ) :
    (k : ℕ) → Transcript (StepMsg F P.numClaims) (SpongeChal P bits) (P.batches + k) →
      Transcript (PcsRbr.Msg F P.numClaims) (GrindChal bits (Chal P.ldt P.queries)) k
  | 0, _ => .nil
  | k + 1, .snoc t m c =>
    (extractPcs P bits k t).snoc (extractStepPcsMsg P (extractBatchFn P t) k m)
      (spongeChalCast P bits c)

/-- Lifted round-by-round `doomed` predicate for the `(P.batches + P.rounds + 2)`-step
incremental sponge protocol. Steps `≤ P.batches` are unconditionally doomed (`True`,
so absorption steps have zero error); steps `P.batches + k` (`k ≥ 1`) delegate
directly to `PcsRbr.grindDoomed`. -/
def spongeDoomed (P : Params F) (bits : ℕ → ℕ) (θ : ℝ) (i : ℕ)
    (t : Transcript (StepMsg F P.numClaims) (SpongeChal P bits) i) : Prop :=
  if h : P.batches < i then
    PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) (i - P.batches)
      (extractPcs P bits (i - P.batches) (cast (by rw [Nat.add_sub_of_le (Nat.le_of_lt h)]) t))
  else True

omit [Fintype F] in
theorem spongeDoomed_nil (P : Params F) (bits : ℕ → ℕ) (θ : ℝ) :
    spongeDoomed P bits θ 0 .nil := by
  simp [spongeDoomed]

omit [Fintype F] in
/-- Evaluating `spongeDoomed` at `P.batches + (k + 1)` directly without casts. -/
theorem spongeDoomed_add_succ (P : Params F) (bits : ℕ → ℕ) (θ : ℝ) (k : ℕ)
    (t : Transcript (StepMsg F P.numClaims) (SpongeChal P bits) (P.batches + (k + 1))) :
    spongeDoomed P bits θ (P.batches + (k + 1)) t ↔
      PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) (k + 1)
        (extractPcs P bits (k + 1) t) := by
  unfold spongeDoomed
  rw [dite_eq_left (by omega)]
  have hsub : P.batches + (k + 1) - P.batches = k + 1 := Nat.add_sub_cancel_left P.batches (k + 1)
  have hgen : ∀ (n : ℕ) (hn : n = k + 1)
      (heq : P.batches + n = P.batches + (k + 1)),
      PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) n
        (extractPcs P bits n (cast (by rw [heq]) t)) ↔
      PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) (k + 1)
        (extractPcs P bits (k + 1) t) := by
    rintro n rfl heq
    rfl
  exact hgen _ hsub (Nat.add_sub_of_le (by omega))

/-- **Round-by-round soundness of the single-root incremental sponge protocol.**
Absorption steps `< P.batches` have error `0`, and steps `P.batches + k` have
error `roundError P.rounds εα εβ θ P.queries k / 2 ^ bits k`. -/
theorem rbrSound_sponge (P : Params F) (bits : ℕ → ℕ) {θ : ℝ} (hθ : 0 ≤ θ)
    {εα εβ : ℕ → ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i)) :
    RbrSound (P.batches + (P.rounds + 2)) (spongeDoomed P bits θ)
      (fun i => if i < P.batches then 0
        else roundError P.rounds εα εβ θ P.queries (i - P.batches) / 2 ^ bits (i - P.batches)) := by
  have hrbr := PcsRbr.rbrSound_grind P.ldt P.shift_ne hθ P.queries hmca hstep bits
  intro i hi t m hdoom
  by_cases hlt : i < P.batches
  · simp only [hlt, ↓reduceIte]
    refine FractionLE.false.mono_left fun c hc => hc ?_
    unfold spongeDoomed
    rw [dite_eq_right (by omega)]
    trivial
  · simp only [hlt, ↓reduceIte]
    have hge : P.batches ≤ i := Nat.le_of_not_lt hlt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    have hk_lt : k < P.rounds + 2 := by omega
    rw [Nat.add_sub_cancel_left]
    have hdoom0 : PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) k
        (extractPcs P bits k t) := by
      cases k with
      | zero =>
        exact PcsRbr.grindDoomed_nil (PcsRbr.doomed_zero P.ldt P.shift θ P.queries _)
      | succ k' =>
        exact (spongeDoomed_add_succ P bits θ k' t).mp hdoom
    have hfrac := hrbr k hk_lt (extractPcs P bits k t)
      (extractStepPcsMsg P (extractBatchFn P t) k m) hdoom0
    obtain ⟨S, hScard, hSmem⟩ := hfrac
    refine ⟨S.map ⟨spongeChalOf P bits, fun a b hab => by
        have := congrArg (spongeChalCast P bits) hab
        simpa [spongeChalCast_of] using this⟩, ?_, fun c hc => ?_⟩
    · rw [Finset.card_map]
      have hcardEq : Fintype.card (SpongeChal P bits (P.batches + k)) =
          Fintype.card (GrindChal bits (Chal P.ldt P.queries) k) :=
        Fintype.card_congr
          { toFun := spongeChalCast P bits
            invFun := spongeChalOf P bits
            left_inv := spongeChalOf_cast P bits
            right_inv := spongeChalCast_of P bits }
      rw [hcardEq]
      exact hScard
    · rw [Finset.mem_map]
      refine ⟨spongeChalCast P bits c, hSmem _ ?_, spongeChalOf_cast P bits c⟩
      intro hgood
      apply hc
      exact (spongeDoomed_add_succ P bits θ k (t.snoc m c)).mpr hgood

end CompiledSponge

end CertiFri.Sponge

/-! ## Executable `Fri.verify` soundness under incremental sponge chaining (`c = 3 / 2`) -/

namespace CertiFri.Exec

open Oracle OracleComp Fri Sponge
open PcsRbr (Chal GrindChal ClaimsFail Accepts PowPasses ungrind roundError alphaOf betasOf queriesOf)

section ExecSponge

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Fintype K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- Answer type of the incremental sponge oracle for `Fri.verify` with
single-root absorption (`batches` root-absorption steps + `rounds + 2` FRI
challenge rounds). -/
abbrev SpongeOracleAnswer :=
  SpongeMerkleAnswer (RawMsg F EF D)
    (SpongeChal (modelParams m params shape wf) (powBits params shape)) K D

/-- The `(batches + rounds + 2)` incremental sponge raw messages of an attempt:
* Steps `b < batches`: `[.digest (a.commitments.getD b default)]` (**1 digest!**)
* Step `batches`: `a.points.toList.map .ext ++ a.values.toList.map .ext` (**0 digests!**)
* Steps `batches + 1 + i` (`i < rounds`): `a.messages params shape (1 + i)` (**1 digest!**)
* Step `batches + rounds + 1`: `a.messages params shape (rounds + 1)` (**0 digests!**) -/
def Attempt.spongeMessages (params : FriParams) (shape : ClaimShape) (a : Attempt F EF D)
    (i : ℕ) : RawMsg F EF D :=
  if i < shape.length then [.digest (a.commitments.getD i default)]
  else if i = shape.length then a.points.toList.map .ext ++ a.values.toList.map .ext
  else a.messages params shape (i - shape.length)

/-- Per-step digest list for the incremental sponge oracle (`entryCap = 1`!):
every step `i < batches + rounds + 2` brings at most **1** Merkle digest into play. -/
def spongeStepDigests (P : Compiled.Params K) (i : ℕ) (msg : RawMsg F EF D) : List D :=
  if i < P.batches then [(digestsIn msg).getD 0 default]
  else if i = P.batches then []
  else if i ≤ P.batches + P.rounds then [(digestsIn msg).getD 0 default]
  else []

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K] [DecidableEq K]
  [DecidableEq D] in
theorem length_spongeStepDigests_le_one (P : Compiled.Params K) (i : ℕ) (msg : RawMsg F EF D) :
    (spongeStepDigests (F := F) (EF := EF) P i msg).length ≤ 1 := by
  unfold spongeStepDigests
  split_ifs <;> simp

/-- Step message reader against committed rows `c`: depends ONLY on the
`≤ 1` digest in `spongeStepDigests P i msg`. -/
noncomputable def spongeStepRead (i : ℕ) (msg : RawMsg F EF D)
    (c : D → Array Dimensions → ℕ → ℕ → Option (Array K)) :
    StepMsg K (modelParams m params shape wf).numClaims :=
  let P := modelParams m params shape wf
  if i < P.batches then .batchRoot (c ((digestsIn msg).getD 0 default))
  else if i = P.batches then
    let v := view m params shape msg
    .round0Meta v.points v.values
  else
    .pcs (P.read (i - P.batches) (view m params shape msg) c)

omit [Fintype K] [DecidableEq D] in
theorem spongeStepRead_congr (i : ℕ) (msg : RawMsg F EF D)
    (c c' : D → Array Dimensions → ℕ → ℕ → Option (Array K))
    (hc : ∀ root ∈ spongeStepDigests (modelParams m params shape wf) i msg, c root = c' root) :
    spongeStepRead m params shape wf i msg c = spongeStepRead m params shape wf i msg c' := by
  unfold spongeStepRead spongeStepDigests at *
  dsimp only
  split_ifs with h1 h2
  · simp only [h1, ↓reduceIte, List.mem_singleton, forall_eq] at hc
    rw [hc]
  · rfl
  · by_cases h3 : i ≤ (modelParams m params shape wf).batches + (modelParams m params shape wf).rounds
    · simp only [h1, h2, h3, ↓reduceIte, List.mem_singleton, forall_eq] at hc
      congr 1
      refine (modelParams m params shape wf).read_congr (i - (modelParams m params shape wf).batches)
        (view m params shape msg) c c' fun root hroot => ?_
      have hne0 : i - (modelParams m params shape wf).batches ≠ 0 := by omega
      have hle : i - (modelParams m params shape wf).batches ≤ (modelParams m params shape wf).rounds := by omega
      simp only [Compiled.digestsOfAt, hne0, ↓reduceIte, hle, List.mem_singleton] at hroot
      subst hroot
      exact hc
    · congr 1
      refine (modelParams m params shape wf).read_congr (i - (modelParams m params shape wf).batches)
        (view m params shape msg) c c' fun root hroot => ?_
      have hgt : ¬ (i - (modelParams m params shape wf).batches ≤ (modelParams m params shape wf).rounds) := by omega
      have hne0 : i - (modelParams m params shape wf).batches ≠ 0 := by omega
      simp [Compiled.digestsOfAt, hne0, hgt] at hroot

/-- Extract the `k`-round `GrindChal` transcript from the incremental sponge
transcript of an attempt, mapping round `j` to `f_view j`. -/
def spongeToGrindTranscript {P : Compiled.Params K} {bits : ℕ → ℕ} {M' : Type}
    (f_view : ℕ → M') :
    (k : ℕ) → Oracle.Transcript (RawMsg F EF D) (SpongeChal P bits) (P.batches + k) →
      Oracle.Transcript M' (GrindChal bits (Chal P.ldt P.queries)) k
  | 0, _ => .nil
  | k + 1, .snoc t _ c =>
    (spongeToGrindTranscript f_view k t).snoc (f_view k) (spongeChalCast P bits c)

/-- State of the idealised incremental sponge challenger. -/
structure SpongeState (F EF D : Type) where
  step : ℕ
  chain : D
  cur : RawMsg F EF D
  nsamp : ℕ

def SpongeState.init (s₀ : D) : SpongeState F EF D := ⟨0, s₀, [], 0⟩

/-- Query the sponge oracle at the current step and cast to `GrindChal`. -/
def spongeAnswer (P : Compiled.Params K) (bits : ℕ → ℕ)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    (s : SpongeState F EF D) : GrindChal bits (Chal P.ldt P.queries) (s.step - P.batches) :=
  if h : P.batches ≤ s.step then
    spongeChalCast P bits (cast (by rw [Nat.add_sub_of_le h]) (f (.chal s.step s.chain s.cur)).2)
  else
    have h0 : s.step - P.batches = 0 := Nat.sub_eq_zero_of_le (by omega)
    cast (by rw [h0]) (spongeChalCast P bits (k := 0)
      (cast (by rw [Nat.add_zero]) (f (.chal P.batches s.chain s.cur)).2))

/-- Hasher from a sponge oracle function `f`. -/
def spongeHasherOf {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x) : MerkleHasher K D where
  hashRows xs := f (.other (.rows xs))
  compress a b := f (.other (.node a b))

/-- **Idealised incremental sponge challenger** matching `Fri.verify` and
single-root absorption (`entryCap = 1`). -/
noncomputable def spongeChallenger (P : Compiled.Params K) (bits : ℕ → ℕ)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    (m : FieldModel F EF K) : Challenger (SpongeState F EF D) F EF D where
  observe s o :=
    if s.nsamp = 0 then
      if s.step < P.batches then
        ⟨s.step + 1, (f (.chal s.step s.chain [o])).1, [], 0⟩
      else
        { s with cur := s.cur ++ [o] }
    else
      ⟨s.step + 1, (f (.chal s.step s.chain s.cur)).1, [o], 0⟩
  sampleExt s :=
    (Function.surjInv m.surj (spongeAnswer P bits f s).2.field, { s with nsamp := s.nsamp + 1 })
  sampleBits s _ :=
    (if s.nsamp = 0 ∧ bits (s.step - P.batches) ≠ 0 then ((spongeAnswer P bits f s).1 : ℕ)
      else P.indexOf (queryPoint P (spongeAnswer P bits f s).2
        (s.nsamp - if bits (s.step - P.batches) = 0 then 0 else 1)),
      { s with nsamp := s.nsamp + 1 })

/-- **Executable `Fri.verify` against an incremental sponge oracle `f` from `s₀`.** -/
noncomputable def spongeAccepts (s₀ : D)
    (f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D) : Bool :=
  Fri.verify (merkleMmcs (inputHasher m (spongeHasherOf f)))
    (merkleMmcs (friHasher m (spongeHasherOf f)))
    (spongeChallenger (modelParams m params shape wf) (powBits params shape) f m)
    (SpongeState.init s₀) params shape a.commitments a.points a.values a.proof

/-! ## Simulation between `spongeChallenger` and `freeChallenger` -/

private def foldSpongeList {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) : List (Observation F EF D) → ℕ × D
  | [] => (step, chain)
  | o :: rest => foldSpongeList f (step + 1) (f (.chal step chain [o])).1 rest

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem foldSpongeList_append {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) (xs ys : List (Observation F EF D)) :
    foldSpongeList f step chain (xs ++ ys) =
      let p := foldSpongeList f step chain xs
      foldSpongeList f p.1 p.2 ys := by
  induction xs generalizing step chain with
  | nil => rfl
  | cons o xs ih => exact ih (step + 1) (f (.chal step chain [o])).1

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem foldSpongeList_fst {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) (xs : List (Observation F EF D)) :
    (foldSpongeList f step chain xs).1 = step + xs.length := by
  induction xs generalizing step chain with
  | nil => simp [foldSpongeList]
  | cons o xs ih =>
    simp only [foldSpongeList, List.length_cons]
    rw [ih]
    omega

/-- Sponge state reached by running `f` along the `i` rounds of a full transcript `t`. -/
def transcriptSpongeState (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x) :
    {i : ℕ} → Oracle.Transcript (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) i → D
  | 0, .nil => s₀
  | 1, .snoc .nil m₀ _ =>
    let st := (foldSpongeList f 0 s₀ (m₀.take P.batches)).2
    (f (.chal P.batches st (m₀.drop P.batches))).1
  | i + 2, .snoc t m _ =>
    let prev := transcriptSpongeState P bits s₀ f t
    (f (.chal (P.batches + (i + 1)) prev m)).1

/-- Lift a sponge oracle `f` to the induced full-transcript `FSQuery` oracle. -/
def liftSpongeOracle (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x) :
    ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) K D x
  | .other q => f (.other q)
  | .chal (i := 0) .nil m =>
    let st := (foldSpongeList f 0 s₀ (m.take P.batches)).2
    spongeChalCast P bits (f (.chal P.batches st (m.drop P.batches))).2
  | .chal (i := k + 1) t m =>
    let prev := transcriptSpongeState P bits s₀ f t
    spongeChalCast P bits (f (.chal (P.batches + (k + 1)) prev m)).2

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K]
  [DecidableEq D] [Inhabited D] in
theorem hasherOf_liftSpongeOracle (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x) :
    hasherOf (liftSpongeOracle P bits s₀ f) = spongeHasherOf f := rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem drop_firstMessage_eq (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    (firstMessage (F := F) a.commitments a.points a.values).drop shape.length =
      a.points.toList.map .ext ++ a.values.toList.map .ext := by
  simp only [firstMessage, List.append_assoc]
  have hlen : (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))).length =
      shape.length := by
    simp [hcomm]
  rw [← hlen]
  exact List.drop_left' rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem spongeTranscript_succ_fst {M : Type} {C : ℕ → Type} {O : Type}
    {A : O → Type} (f : ∀ x : SpongeQuery M D O, SpongeAnswer C D A x)
    (s₀ : D) (msgs : ℕ → M) (i : ℕ) :
    (spongeTranscript f s₀ msgs (i + 1)).1 =
      (spongeTranscript f s₀ msgs i).1.snoc (msgs i)
        (f (.chal i (spongeTranscript f s₀ msgs i).2 (msgs i))).2 := by
  change (match spongeTranscript f s₀ msgs i with
    | (t, prev) =>
      match f (.chal i prev (msgs i)) with
      | (next, c) => (t.snoc (msgs i) c, next)).1 = _
  rcases spongeTranscript f s₀ msgs i with ⟨t, prev⟩
  dsimp only
  rcases f (.chal i prev (msgs i)) with ⟨next, c⟩
  rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem spongeTranscript_succ_snd {M : Type} {C : ℕ → Type} {O : Type}
    {A : O → Type} (f : ∀ x : SpongeQuery M D O, SpongeAnswer C D A x)
    (s₀ : D) (msgs : ℕ → M) (i : ℕ) :
    (spongeTranscript f s₀ msgs (i + 1)).2 =
      (f (.chal i (spongeTranscript f s₀ msgs i).2 (msgs i))).1 := by
  change (match spongeTranscript f s₀ msgs i with
    | (t, prev) =>
      match f (.chal i prev (msgs i)) with
      | (next, c) => (t.snoc (msgs i) c, next)).2 = _
  rcases spongeTranscript f s₀ msgs i with ⟨t, prev⟩
  dsimp only
  rcases f (.chal i prev (msgs i)) with ⟨next, c⟩
  rfl

omit [Fintype K] [DecidableEq D] in
private theorem spongeTranscript_prefix_eq (s₀ : D)
    (f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    ∀ k ≤ shape.length,
      (spongeTranscript f s₀ (a.spongeMessages params shape) k).2 =
        (foldSpongeList f 0 s₀ ((firstMessage (F := F) a.commitments a.points a.values).take k)).2
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := spongeTranscript_prefix_eq s₀ f a hcomm k (by omega)
    have htake : (firstMessage (F := F) a.commitments a.points a.values).take (k + 1) =
        (firstMessage (F := F) a.commitments a.points a.values).take k ++
          [.digest (a.commitments.getD k default)] := by
      have hklt : k < (firstMessage (F := F) a.commitments a.points a.values).length := by
        simp [firstMessage, hcomm]; omega
      rw [List.take_succ_eq_append_getElem hklt]
      congr 1
      have hltc : k < (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))).length := by
        simp [hcomm]; omega
      simp only [firstMessage, List.append_assoc, List.getElem_append_left hltc, List.getElem_map]
      simp [Array.getD, show k < a.commitments.size by omega]
    rw [htake, foldSpongeList_append]
    dsimp only
    have hfst : (foldSpongeList f 0 s₀
        ((firstMessage (F := F) a.commitments a.points a.values).take k)).1 = k := by
      rw [foldSpongeList_fst, Nat.zero_add, List.length_take, Nat.min_eq_left]
      simp [firstMessage, hcomm]; omega
    have hmsg : a.spongeMessages params shape k = [.digest (a.commitments.getD k default)] := by
      unfold Attempt.spongeMessages
      rw [ite_eq_left (by omega)]
    rw [hfst, foldSpongeList, foldSpongeList, spongeTranscript_succ_snd, ih, hmsg]

omit [Fintype K] [DecidableEq D] in
private theorem spongeTranscript_eq_lift (s₀ : D)
    (f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    ∀ k,
      (spongeTranscript f s₀ (a.spongeMessages params shape) (shape.length + k)).2 =
        (if k = 0 then
          (foldSpongeList f 0 s₀
            ((firstMessage (F := F) a.commitments a.points a.values).take shape.length)).2
        else
          transcriptSpongeState (modelParams m params shape wf) (powBits params shape) s₀ f
            (fsTranscript (liftSpongeOracle (modelParams m params shape wf) (powBits params shape) s₀ f)
              (a.messages params shape) k))
  | 0 => by
    simp only [Nat.add_zero, ↓reduceIte]
    exact spongeTranscript_prefix_eq m params shape wf s₀ f a hcomm shape.length le_rfl
  | 1 => by
    have h0 := spongeTranscript_prefix_eq m params shape wf s₀ f a hcomm shape.length le_rfl
    have hmsg : a.spongeMessages params shape shape.length =
        (firstMessage (F := F) a.commitments a.points a.values).drop shape.length := by
      rw [drop_firstMessage_eq shape a hcomm]
      unfold Attempt.spongeMessages
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    rw [spongeTranscript_succ_snd, h0, hmsg]
    rfl
  | k + 2 => by
    have ih := spongeTranscript_eq_lift s₀ f a hcomm (k + 1)
    simp only [Nat.succ_ne_zero, ↓reduceIte] at ih ⊢
    have hmsg : a.spongeMessages params shape (shape.length + (k + 1)) =
        a.messages params shape (k + 1) := by
      unfold Attempt.spongeMessages
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    rw [show shape.length + (k + 2) = (shape.length + (k + 1)) + 1 by omega,
      spongeTranscript_succ_snd, ih, hmsg]
    rfl

/-- Simulation relation between `FreeState` (under `liftSpongeOracle`) and
`SpongeState` (under `spongeChallenger`). -/
private def StateRel (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    (fs : FreeState F EF D) (ss : SpongeState F EF D) : Prop :=
  (fs.round = 0 ∧ fs.nsamp = 0 ∧ fs.cur.length ≤ P.batches ∧
    ss = ⟨fs.cur.length, (foldSpongeList f 0 s₀ fs.cur).2, [], 0⟩) ∨
  (fs.round = 0 ∧ P.batches ≤ fs.cur.length ∧
    ss = ⟨P.batches, (foldSpongeList f 0 s₀ (fs.cur.take P.batches)).2,
      fs.cur.drop P.batches, fs.nsamp⟩) ∨
  (1 ≤ fs.round ∧
    ss = ⟨P.batches + fs.round,
      transcriptSpongeState P bits s₀ f
        (fsTranscript (liftSpongeOracle P bits s₀ f) fs.hist fs.round),
      fs.cur, fs.nsamp⟩)

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRel_observe (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRel P bits s₀ f fs ss) (o : Observation F EF D) :
    StateRel P bits s₀ f
      ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe fs o)
      ((spongeChallenger P bits f m).observe ss o) := by
  rcases fs with ⟨round, hist, cur, nsamp⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · dsimp only at hr hns hlen
    have hobs_f : (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
        ⟨round, hist, cur, nsamp⟩ o = ⟨round, hist, cur ++ [o], nsamp⟩ := by
      simp [freeChallenger, hns]
    rw [hobs_f]
    by_cases hlt : cur.length < P.batches
    · left
      simp only [spongeChallenger, hlt, ↓reduceIte, List.length_append, List.length_singleton]
      refine ⟨hr, hns, by omega, ?_⟩
      rw [foldSpongeList_append]
      dsimp only
      rw [foldSpongeList_fst, Nat.zero_add]
      rfl
    · right; left
      have heq : cur.length = P.batches := by omega
      simp only [spongeChallenger, hlt, ↓reduceIte, List.length_append, List.length_singleton]
      refine ⟨hr, by omega, ?_⟩
      rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
        ← heq, List.take_length, List.drop_length, List.nil_append]
      simp [hns]
  · dsimp only at hr hlen
    subst hr
    by_cases hns : nsamp = 0
    · have hobs_f : (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
          ⟨0, hist, cur, nsamp⟩ o = ⟨0, hist, cur ++ [o], nsamp⟩ := by
        simp [freeChallenger, hns]
      rw [hobs_f]
      right; left
      simp only [spongeChallenger, hns, ↓reduceIte, lt_irrefl,
        List.length_append, List.length_singleton]
      refine ⟨trivial, by omega, ?_⟩
      rw [List.take_append_of_le_length hlen, List.drop_append_of_le_length hlen]
    · have hobs_f : (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
          ⟨0, hist, cur, nsamp⟩ o = ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
        simp [freeChallenger, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallenger, hns, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      simp only [fsTranscript, Function.update_self]
      rfl
  · dsimp only at hr
    by_cases hns : nsamp = 0
    · have hobs_f : (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
          ⟨round, hist, cur, nsamp⟩ o = ⟨round, hist, cur ++ [o], nsamp⟩ := by
        simp [freeChallenger, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallenger, hns, ↓reduceIte,
        show ¬ (P.batches + round < P.batches) by omega]
      exact ⟨hr, trivial⟩
    · have hobs_f : (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
          ⟨round, hist, cur, nsamp⟩ o = ⟨round + 1, Function.update hist round cur, [o], 0⟩ := by
        simp [freeChallenger, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallenger, hns, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
      have hr' : round = k + 1 := by omega
      have hcongr : fsTranscript (liftSpongeOracle P bits s₀ f)
          (Function.update hist round cur) round =
          fsTranscript (liftSpongeOracle P bits s₀ f) hist round :=
        Transcript.fsTranscript_congr _ fun j hj => Function.update_of_ne (by omega) _ _
      have heq_step : P.batches + round + 1 = P.batches + (round + 1) := by omega
      rw [heq_step]
      congr 1
      have hst : transcriptSpongeState P bits s₀ f
          (fsTranscript (liftSpongeOracle P bits s₀ f)
            (Function.update hist round cur) (round + 1)) =
          (f (.chal (P.batches + round)
            (transcriptSpongeState P bits s₀ f
              (fsTranscript (liftSpongeOracle P bits s₀ f) hist round)) cur)).1 := by
        rw [← hcongr]
        generalize hist = hh at *
        let t0 := fsTranscript (liftSpongeOracle P bits s₀ f)
            (Function.update hh round cur) round
        have hstep : fsTranscript (liftSpongeOracle P bits s₀ f)
            (Function.update hh round cur) (round + 1) =
            t0.snoc cur (liftSpongeOracle P bits s₀ f (.chal t0 cur)) := by
          have hupd : Function.update hh round cur round = cur := Function.update_self round cur hh
          show t0.snoc (Function.update hh round cur round)
              (liftSpongeOracle P bits s₀ f (.chal t0 (Function.update hh round cur round))) =
            t0.snoc cur (liftSpongeOracle P bits s₀ f (.chal t0 cur))
          rw [hupd]
        rw [hstep]
        have h1 : ∀ (n : ℕ) (hn : n = k + 1)
            (t : Oracle.Transcript (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) n)
            (msg : RawMsg F EF D) (c : GrindChal bits (Chal P.ldt P.queries) n),
            transcriptSpongeState P bits s₀ f (t.snoc msg c) =
              (f (.chal (P.batches + n) (transcriptSpongeState P bits s₀ f t) msg)).1 := by
          rintro n rfl t msg c
          rfl
        exact h1 round hr' t0 cur (liftSpongeOracle P bits s₀ f (.chal t0 cur))
      exact hst.symm

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRel_observeAll (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    (obs : List (Observation F EF D)) {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRel P bits s₀ f fs ss) :
    StateRel P bits s₀ f
      ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observeAll fs obs)
      ((spongeChallenger P bits f m).observeAll ss obs) := by
  induction obs generalizing fs ss with
  | nil => exact hrel
  | cons o obs ih => exact ih (stateRel_observe m P bits s₀ f hrel o)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K] [DecidableEq D]
  [Inhabited D] in
private theorem freeAnswer_eq_spongeAnswer (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRel P bits s₀ f fs ss) (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) :
    ss.step - P.batches = fs.round ∧
      HEq (freeAnswer P bits (liftSpongeOracle P bits s₀ f) fs) (spongeAnswer P bits f ss) := by
  rcases fs with ⟨round, hist, cur, nsamp⟩
  dsimp only at hready hrel ⊢
  rcases hrel with ⟨hr, _, hlen, rfl⟩ | ⟨hr, _, rfl⟩ | ⟨hr, rfl⟩
  · subst hr
    dsimp only at hready hlen
    have heq : cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    have htake : cur.take P.batches = cur := by rw [← heq, List.take_length]
    have hdrop : cur.drop P.batches = [] := by rw [← heq, List.drop_length]
    have hss : (⟨cur.length, (foldSpongeList f 0 s₀ cur).2, [], 0⟩ : SpongeState F EF D) =
        ⟨P.batches, (foldSpongeList f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ := by
      simp [heq, htake, hdrop]
    rw [hss]
    refine ⟨by simp, ?_⟩
    unfold freeAnswer spongeAnswer
    simp only [le_rfl, ↓reduceDIte, fsTranscript, liftSpongeOracle]
    have hzero : P.batches - P.batches = 0 := Nat.sub_self P.batches
    have hgen : ∀ (n : ℕ) (hn : n = 0)
        (a : SpongeChal P bits (P.batches + n))
        (b : SpongeChal P bits (P.batches + 0)),
        HEq a b →
        HEq (spongeChalCast P bits b) (spongeChalCast P bits a) := by
      rintro n rfl a b hab
      rw [eq_of_heq hab]
    exact hgen (P.batches - P.batches) hzero _ _ (cast_heq _ _)
  · subst hr
    refine ⟨by simp, ?_⟩
    unfold freeAnswer spongeAnswer
    simp only [le_rfl, ↓reduceDIte, fsTranscript, liftSpongeOracle]
    have hzero : P.batches - P.batches = 0 := Nat.sub_self P.batches
    have hgen : ∀ (n : ℕ) (hn : n = 0)
        (a : SpongeChal P bits (P.batches + n))
        (b : SpongeChal P bits (P.batches + 0)),
        HEq a b →
        HEq (spongeChalCast P bits b) (spongeChalCast P bits a) := by
      rintro n rfl a b hab
      rw [eq_of_heq hab]
    exact hgen (P.batches - P.batches) hzero _ _ (cast_heq _ _)
  · dsimp only at hr
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
    have hr' : round = k + 1 := by omega
    subst hr'
    refine ⟨by dsimp only; omega, ?_⟩
    unfold freeAnswer spongeAnswer
    simp only [show P.batches ≤ P.batches + (k + 1) by omega, ↓reduceDIte, liftSpongeOracle]
    have hstep : P.batches + (k + 1) - P.batches = k + 1 := Nat.add_sub_cancel_left _ _
    have hgen2 : ∀ (n : ℕ) (hn : n = k + 1)
        (c : SpongeChal P bits (P.batches + n)),
        HEq c (f (.chal (P.batches + (k + 1))
          (transcriptSpongeState P bits s₀ f
            (fsTranscript (liftSpongeOracle P bits s₀ f) hist (k + 1))) cur)).2 →
        HEq (spongeChalCast P bits (f (.chal (P.batches + (k + 1))
          (transcriptSpongeState P bits s₀ f
            (fsTranscript (liftSpongeOracle P bits s₀ f) hist (k + 1))) cur)).2)
            (spongeChalCast P bits c) := by
      rintro n rfl c hc
      rw [eq_of_heq hc]
    exact hgen2 _ hstep _ (cast_heq _ _)

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRel_sampleExt (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRel P bits s₀ f fs ss) (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) :
    ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).sampleExt fs).1 =
      ((spongeChallenger P bits f m).sampleExt ss).1 ∧
    StateRel P bits s₀ f
      ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).sampleExt fs).2
      ((spongeChallenger P bits f m).sampleExt ss).2 := by
  obtain ⟨hstep, hans⟩ := freeAnswer_eq_spongeAnswer P bits s₀ f hrel hready
  have hval : (freeAnswer P bits (liftSpongeOracle P bits s₀ f) fs).2.field =
      (spongeAnswer P bits f ss).2.field := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (Chal P.ldt P.queries) a)
        (y : GrindChal bits (Chal P.ldt P.queries) b),
        HEq x y → x.2.field = y.2.field := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  refine ⟨by simp [freeChallenger, spongeChallenger, hval], ?_⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · have heq : fs.cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    right; left
    refine ⟨hr, by dsimp only [freeChallenger]; omega, ?_⟩
    simp only [freeChallenger, spongeChallenger, heq, hns]
    rw [← heq, List.take_length, List.drop_length]
  · right; left; exact ⟨hr, hlen, rfl⟩
  · right; right; exact ⟨hr, rfl⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRel_sampleBits (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRel P bits s₀ f fs ss) (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length)
    (nbits : ℕ) :
    ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).sampleBits fs nbits).1 =
      ((spongeChallenger P bits f m).sampleBits ss nbits).1 ∧
    StateRel P bits s₀ f
      ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).sampleBits fs nbits).2
      ((spongeChallenger P bits f m).sampleBits ss nbits).2 := by
  obtain ⟨hstep, hans⟩ := freeAnswer_eq_spongeAnswer P bits s₀ f hrel hready
  have hns_eq : fs.nsamp = ss.nsamp := by
    rcases hrel with ⟨_, hns, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
    · exact hns
    · rfl
    · rfl
  have hfst : ((freeAnswer P bits (liftSpongeOracle P bits s₀ f) fs).1 : ℕ) =
      ((spongeAnswer P bits f ss).1 : ℕ) := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (Chal P.ldt P.queries) a)
        (y : GrindChal bits (Chal P.ldt P.queries) b),
        HEq x y → (x.1 : ℕ) = (y.1 : ℕ) := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  have hqp : ∀ k, queryPoint P (freeAnswer P bits (liftSpongeOracle P bits s₀ f) fs).2 k =
      queryPoint P (spongeAnswer P bits f ss).2 k := by
    intro k
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (Chal P.ldt P.queries) a)
        (y : GrindChal bits (Chal P.ldt P.queries) b),
        HEq x y → queryPoint P x.2 k = queryPoint P y.2 k := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  refine ⟨by simp [freeChallenger, spongeChallenger, hstep, hns_eq, hfst, hqp], ?_⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · have heq : fs.cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    right; left
    refine ⟨hr, by dsimp only [freeChallenger]; omega, ?_⟩
    simp only [freeChallenger, spongeChallenger, heq, hns]
    rw [← heq, List.take_length, List.drop_length]
  · right; left; exact ⟨hr, hlen, rfl⟩
  · right; right; exact ⟨hr, rfl⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRel_checkWitness (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRel P bits s₀ f fs ss) (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length)
    (powBits : ℕ) (w : F) :
    ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).checkWitness fs powBits w).1 =
      ((spongeChallenger P bits f m).checkWitness ss powBits w).1 ∧
    StateRel P bits s₀ f
      ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).checkWitness fs powBits w).2
      ((spongeChallenger P bits f m).checkWitness ss powBits w).2 ∧
    (1 ≤ ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).checkWitness fs powBits w).2.round ∨
      P.batches ≤ ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).checkWitness fs powBits w).2.cur.length) := by
  unfold Challenger.checkWitness
  have hokF : ∀ s, (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).ok s = true :=
    fun _ => rfl
  have hokS : ∀ s, (spongeChallenger P bits f m).ok s = true := fun _ => rfl
  simp only [hokF, hokS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
  split_ifs with h0
  · exact ⟨rfl, hrel, hready⟩
  · have hobs := stateRel_observe m P bits s₀ f hrel (.base w)
    have hready' : 1 ≤ ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe fs (.base w)).round ∨
        P.batches ≤ ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe fs (.base w)).cur.length := by
      simp only [freeChallenger]
      split_ifs
      · rcases hready with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by dsimp only; simp; omega)
      · exact Or.inl (by dsimp only; omega)
    obtain ⟨hb1, hb2⟩ := stateRel_sampleBits m P bits s₀ f hobs hready' powBits
    exact ⟨by simp [hb1], hb2, hready'⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRel_sampleIndices (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    (nbits : ℕ) : ∀ (count : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRel P bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).sampleIndices nbits count fs =
        (spongeChallenger P bits f m).sampleIndices nbits count ss
  | 0, _, _, _, _ => rfl
  | count + 1, fs, ss, hrel, hready => by
    simp only [Challenger.sampleIndices]
    obtain ⟨h1, h2⟩ := stateRel_sampleBits m P bits s₀ f hrel hready nbits
    rw [h1, stateRel_sampleIndices P bits s₀ f nbits count h2 hready]

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] in
private theorem stateRel_commitPhase (P : Compiled.Params K) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChal P bits) K D x)
    (commitPowBits : ℕ) (commits : Array D) (witnesses : Array F) :
    ∀ (rounds : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRel P bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (commitPhase (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).1 =
        (commitPhase (spongeChallenger P bits f m)
          commitPowBits commits witnesses rounds ss).1 ∧
      (commitPhase (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.1 =
        (commitPhase (spongeChallenger P bits f m)
          commitPowBits commits witnesses rounds ss).2.1 ∧
      StateRel P bits s₀ f
        (commitPhase (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2
        (commitPhase (spongeChallenger P bits f m)
          commitPowBits commits witnesses rounds ss).2.2 ∧
      (1 ≤ (commitPhase (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2.round ∨
        P.batches ≤ (commitPhase (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2.cur.length)
  | 0, _, _, hrel, hready => ⟨rfl, rfl, hrel, hready⟩
  | r + 1, fs, ss, hrel, hready => by
    obtain ⟨h1, h2, h3, h4⟩ := stateRel_commitPhase P bits s₀ f commitPowBits commits witnesses r hrel hready
    simp only [commitPhase]
    let fs_prev := (commitPhase (freeChallenger P bits (liftSpongeOracle P bits s₀ f) m)
        commitPowBits commits witnesses r fs).2.2
    have hobs := stateRel_observe m P bits s₀ f h3 (.digest (commits.getD r default))
    have hready' : 1 ≤ ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
          fs_prev (.digest (commits.getD r default))).round ∨
        P.batches ≤ ((freeChallenger P bits (liftSpongeOracle P bits s₀ f) m).observe
          fs_prev (.digest (commits.getD r default))).cur.length := by
      simp only [freeChallenger]
      split_ifs
      · rcases h4 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (by dsimp only [fs_prev] at *; simp; omega)
      · exact Or.inl (by dsimp only; omega)
    obtain ⟨hw1, hw2, hw3⟩ := stateRel_checkWitness m P bits s₀ f hobs hready' commitPowBits (witnesses.getD r 0)
    obtain ⟨he1, he2⟩ := stateRel_sampleExt m P bits s₀ f hw2 hw3
    exact ⟨by rw [h1, he1], by rw [h2, hw1], he2, hw3⟩

omit [Fintype K] in
/-- **Exact refinement of `spongeAccepts` to `Exec.accepts (liftSpongeOracle ...)`!** -/
theorem accepts_liftSpongeOracle_of_spongeAccepts (s₀ : D)
    (f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (h : spongeAccepts m params shape wf s₀ f a = true) :
    accepts m params shape wf
      (liftSpongeOracle (modelParams m params shape wf) (powBits params shape) s₀ f) a = true := by
  unfold spongeAccepts Fri.verify at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hshape, hwith⟩ := h
  have hcomm : a.commitments.size = shape.length := by
    unfold Fri.shapeOk at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.1.2
  let P := modelParams m params shape wf
  let bits := powBits params shape
  let fl := liftSpongeOracle P bits s₀ f
  have hinit : StateRel P bits s₀ f FreeState.init (SpongeState.init s₀) := by
    left; exact ⟨rfl, rfl, Nat.zero_le _, rfl⟩
  have hfirst := stateRel_observeAll m P bits s₀ f
    (firstMessage (F := F) a.commitments a.points a.values) hinit
  have hready0 : 1 ≤ ((freeChallenger P bits fl m).observeAll FreeState.init
      (firstMessage (F := F) a.commitments a.points a.values)).round ∨
      P.batches ≤ ((freeChallenger P bits fl m).observeAll FreeState.init
      (firstMessage (F := F) a.commitments a.points a.values)).cur.length := by
    right
    have hobs_cur : ∀ (obs : List (Observation F EF D)) (fs : FreeState F EF D),
        fs.nsamp = 0 →
        ((freeChallenger P bits fl m).observeAll fs obs).cur = fs.cur ++ obs ∧
        ((freeChallenger P bits fl m).observeAll fs obs).nsamp = 0 := by
      intro obs
      induction obs with
      | nil => intro fs hns; simp [Challenger.observeAll, hns]
      | cons o obs ih =>
        intro fs hns
        have hstep : (freeChallenger P bits fl m).observeAll fs (o :: obs) =
            (freeChallenger P bits fl m).observeAll { fs with cur := fs.cur ++ [o] } obs := by
          simp [Challenger.observeAll, freeChallenger, hns]
        rw [hstep]
        obtain ⟨hcur, hns'⟩ := ih { fs with cur := fs.cur ++ [o] } hns
        exact ⟨by simpa [List.append_assoc] using hcur, hns'⟩
    have hc := (hobs_cur (firstMessage (F := F) a.commitments a.points a.values) FreeState.init rfl).1
    rw [hc]
    simp [FreeState.init, firstMessage, P, modelParams, hcomm]
  obtain ⟨hα1, hα2⟩ := stateRel_sampleExt m P bits s₀ f hfirst hready0
  obtain ⟨hc1, hc2, hc3, hc4⟩ := stateRel_commitPhase m P bits s₀ f params.commitPowBits
    a.proof.commitPhaseCommits a.proof.commitPowWitnesses (numRounds params shape) hα2 hready0
  have hfin := stateRel_observeAll m P bits s₀ f
    (finalMessage (F := F) (D := D) (numRounds params shape) a.proof.finalPoly) hc3
  let fs_c := (commitPhase (freeChallenger P bits fl m) params.commitPowBits
    a.proof.commitPhaseCommits a.proof.commitPowWitnesses (numRounds params shape)
    ((freeChallenger P bits fl m).sampleExt ((freeChallenger P bits fl m).observeAll FreeState.init
      (firstMessage (F := F) a.commitments a.points a.values))).2).2.2
  have hready_fin : 1 ≤ ((freeChallenger P bits fl m).observeAll fs_c
      (finalMessage (F := F) (D := D) (numRounds params shape) a.proof.finalPoly)).round ∨
      P.batches ≤ ((freeChallenger P bits fl m).observeAll fs_c
      (finalMessage (F := F) (D := D) (numRounds params shape) a.proof.finalPoly)).cur.length := by
    have hpres : ∀ (obs : List (Observation F EF D)) (fs : FreeState F EF D),
        (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
        1 ≤ ((freeChallenger P bits fl m).observeAll fs obs).round ∨
        P.batches ≤ ((freeChallenger P bits fl m).observeAll fs obs).cur.length := by
      intro obs
      induction obs with
      | nil => intro fs h; exact h
      | cons o obs ih =>
        intro fs h
        refine ih _ ?_
        simp only [freeChallenger]
        split_ifs
        · rcases h with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by dsimp only; simp; omega)
        · exact Or.inl (by dsimp only; omega)
    exact hpres _ _ hc4
  obtain ⟨hp1, hp2, hp3⟩ := stateRel_checkWitness m P bits s₀ f hfin hready_fin
    params.queryPowBits a.proof.queryPowWitness
  have hidx := stateRel_sampleIndices m P bits s₀ f
    (logMaxHeight params.logBlowup shape) params.numQueries hp2 hp3
  have htr : Fri.transcript (freeChallenger P bits fl m) FreeState.init params shape
      a.commitments a.points a.values a.proof =
      Fri.transcript (spongeChallenger P bits f m) (SpongeState.init s₀) params shape
      a.commitments a.points a.values a.proof := by
    unfold Fri.transcript Fri.transcriptTail
    dsimp only
    rw [hα1, hc1, hc2, hp1, hidx]
  unfold accepts Fri.verify
  rw [Bool.and_eq_true]
  refine ⟨hshape, ?_⟩
  change Fri.verifyWith (merkleMmcs (inputHasher m (hasherOf fl)))
      (merkleMmcs (friHasher m (hasherOf fl))) params shape a.commitments a.points a.values
      a.proof (Fri.transcript (freeChallenger P bits fl m) FreeState.init params shape
        a.commitments a.points a.values a.proof) = true
  rw [htr, hasherOf_liftSpongeOracle P bits s₀ f]
  exact hwith

/-! ## The incremental sponge experiment & executable soundness theorems (`c = 3 / 2`) -/

variable [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D]

/-- Verify a proof against the sponge-derived transcript by lifting `P.verifyWith`
(which only makes hash queries) into `SpongeOracleAnswer`. -/
noncomputable def spongeVerify (a : Attempt F EF D)
    (ts : Oracle.Transcript (RawMsg F EF D)
      (SpongeChal (modelParams m params shape wf) (powBits params shape))
      ((modelParams m params shape wf).batches + ((modelParams m params shape wf).rounds + 2)) × D) :
    OracleComp (SpongeOracleAnswer (D := D) m params shape wf) Bool :=
  let P := modelParams m params shape wf
  let bits := powBits params shape
  let tg := spongeToGrindTranscript (P := P) (bits := bits)
    (fun j => view m params shape (a.messages params shape j)) (P.rounds + 2) ts.1
  if PowPasses tg then
    let tu := ungrind tg
    mapHashToSponge (M := RawMsg F EF D) (C := SpongeChal P bits)
      (P.verifyWith (M := Empty) (C := fun _ => PUnit)
        (modelProof m params shape a.proof) (Compiled.msgAt tu)
        (alphaOf tu) (betasOf tu) (fun k => P.indexOf (queriesOf tu k)))
  else .pure false

omit [Fintype K] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
theorem queryBound_spongeVerify (a : Attempt F EF D)
    (ts : Oracle.Transcript (RawMsg F EF D)
      (SpongeChal (modelParams m params shape wf) (powBits params shape))
      ((modelParams m params shape wf).batches + ((modelParams m params shape wf).rounds + 2)) × D) :
    (spongeVerify m params shape wf a ts).QueryBound
      (modelParams m params shape wf).verifierQueries := by
  unfold spongeVerify
  dsimp only
  split_ifs
  · exact queryBound_mapHashToSponge
      ((modelParams m params shape wf).queryBound_verifyWith _ _ _ _ _)
  · exact queryBound_pure _ _

/-- **The incremental sponge soundness experiment for `Fri.verify`.** -/
noncomputable def spongeExperiment {A : Type*} (s₀ : D)
    (adv : OracleComp (SpongeOracleAnswer (D := D) m params shape wf) A)
    (attempt : A → Attempt F EF D) :
    OracleComp (SpongeOracleAnswer (D := D) m params shape wf) (A × Bool) :=
  (Oracle.spongeExperiment s₀
      ((modelParams m params shape wf).batches + ((modelParams m params shape wf).rounds + 2))
      adv (fun a => (attempt a).spongeMessages params shape)).bind fun out =>
    (spongeVerify m params shape wf (attempt out.1) out.2).bind fun b => .pure (out.1, b)

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
/-- Helper: `spongeToGrindTranscript` of `spongeTranscript f` equals `fsTranscript`
of `liftSpongeOracle f` (up to `view`). -/
private theorem spongeToGrindTranscript_eq_fsTranscript (s₀ : D)
    (f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    ∀ k,
      spongeToGrindTranscript (P := modelParams m params shape wf) (bits := powBits params shape)
        (M' := Compiled.Msg K D (modelParams m params shape wf).batches)
        (fun j => view m params shape (a.messages params shape j)) k
        (spongeTranscript f s₀ (a.spongeMessages params shape)
          ((modelParams m params shape wf).batches + k)).1 =
      (fsTranscript
        (liftSpongeOracle (modelParams m params shape wf) (powBits params shape) s₀ f)
        (a.messages params shape) k).mapIdx (fun _ msg =>
          (view m params shape msg : Compiled.Msg K D (modelParams m params shape wf).batches))
  | 0 => rfl
  | 1 => by
    let P := modelParams m params shape wf
    let bits := powBits params shape
    have h0 : (spongeTranscript f s₀ (a.spongeMessages params shape) P.batches).2 =
        (foldSpongeList f 0 s₀
          ((firstMessage (F := F) a.commitments a.points a.values).take P.batches)).2 :=
      spongeTranscript_prefix_eq m params shape wf s₀ f a hcomm shape.length le_rfl
    have hmsg : a.spongeMessages params shape P.batches =
        (firstMessage (F := F) a.commitments a.points a.values).drop P.batches := by
      change a.spongeMessages params shape shape.length =
        (firstMessage (F := F) a.commitments a.points a.values).drop shape.length
      rw [drop_firstMessage_eq shape a hcomm]
      unfold Attempt.spongeMessages
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    have hsucc := spongeTranscript_succ_fst f s₀ (a.spongeMessages params shape) P.batches
    change spongeToGrindTranscript (P := P) (bits := bits) (M' := Compiled.Msg K D P.batches)
        (fun j => view m params shape (a.messages params shape j)) 1
        (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + 1)).1 = _
    rw [hsucc]
    change Oracle.Transcript.snoc .nil (view m params shape (a.messages params shape 0))
        (spongeChalCast P bits (k := 0) (f (.chal P.batches
          (spongeTranscript f s₀ (a.spongeMessages params shape) P.batches).2
          (a.spongeMessages params shape P.batches))).2) =
      Oracle.Transcript.snoc .nil (view m params shape (a.messages params shape 0))
        (liftSpongeOracle P bits s₀ f (.chal .nil (a.messages params shape 0)))
    rw [h0, hmsg]
    rfl
  | k + 2 => by
    let P := modelParams m params shape wf
    let bits := powBits params shape
    have ih := spongeToGrindTranscript_eq_fsTranscript s₀ f a hcomm (k + 1)
    have hst : (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))).2 =
        transcriptSpongeState P bits s₀ f
          (fsTranscript (liftSpongeOracle P bits s₀ f) (a.messages params shape) (k + 1)) := by
      have h := spongeTranscript_eq_lift m params shape wf s₀ f a hcomm (k + 1)
      simp only [Nat.succ_ne_zero, ↓reduceIte] at h
      exact h
    have hmsg : a.spongeMessages params shape (P.batches + (k + 1)) =
        a.messages params shape (k + 1) := by
      change a.spongeMessages params shape (shape.length + (k + 1)) = a.messages params shape (k + 1)
      unfold Attempt.spongeMessages
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    have hsucc := spongeTranscript_succ_fst f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))
    change spongeToGrindTranscript (P := P) (bits := bits) (M' := Compiled.Msg K D P.batches)
        (fun j => view m params shape (a.messages params shape j)) (k + 2)
        (spongeTranscript f s₀ (a.spongeMessages params shape) ((P.batches + (k + 1)) + 1)).1 = _
    rw [hsucc]
    change Oracle.Transcript.snoc
        (spongeToGrindTranscript (P := P) (bits := bits) (M' := Compiled.Msg K D P.batches)
          (fun j => view m params shape (a.messages params shape j)) (k + 1)
          (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))).1)
        (view m params shape (a.messages params shape (k + 1)))
        (spongeChalCast P bits (k := k + 1) (f (.chal (P.batches + (k + 1))
          (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))).2
          (a.spongeMessages params shape (P.batches + (k + 1))))).2) =
      Oracle.Transcript.snoc
        ((fsTranscript (liftSpongeOracle P bits s₀ f) (a.messages params shape) (k + 1)).mapIdx
          (fun _ msg => (view m params shape msg : Compiled.Msg K D P.batches)))
        (view m params shape (a.messages params shape (k + 1)))
        (liftSpongeOracle P bits s₀ f
          (.chal (fsTranscript (liftSpongeOracle P bits s₀ f) (a.messages params shape) (k + 1))
            (a.messages params shape (k + 1))))
    rw [ih, hst, hmsg]
    rfl

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
private theorem extractPcs_mapIdx_eq (a : Attempt F EF D)
    (c : D → Array Dimensions → ℕ → ℕ → Option (Array K)) :
    ∀ (k : ℕ)
      (t : Oracle.Transcript (RawMsg F EF D)
        (SpongeChal (modelParams m params shape wf) (powBits params shape))
        ((modelParams m params shape wf).batches + k)),
      t.msgs = (List.range ((modelParams m params shape wf).batches + k)).map
        (a.spongeMessages params shape) →
      extractPcs (modelParams m params shape wf) (powBits params shape) k
          (t.mapIdx fun j msg => spongeStepRead m params shape wf j msg c) =
        (spongeToGrindTranscript (P := modelParams m params shape wf) (bits := powBits params shape)
            (M' := Compiled.Msg K D (modelParams m params shape wf).batches)
            (fun j => view m params shape (a.messages params shape j)) k t).mapIdx
          fun j msg => (modelParams m params shape wf).read j msg c
  | 0, _, _ => rfl
  | k + 1, .snoc t' msg chal, hmsgs => by
    let P := modelParams m params shape wf
    let bits := powBits params shape
    have hmsgs' : t'.msgs = (List.range (P.batches + k)).map (a.spongeMessages params shape) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, show P.batches + (k + 1) = P.batches + k + 1 by omega,
        List.range_succ, List.map_append, List.map_singleton] at h1
      exact (List.append_inj h1 (by rw [t'.length_msgs, List.length_map, List.length_range]; rfl)).1
    have hmsg_eq : msg = a.spongeMessages params shape (P.batches + k) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, show P.batches + (k + 1) = P.batches + k + 1 by omega,
        List.range_succ, List.map_append, List.map_singleton] at h1
      have hlast := (List.append_inj h1 (by rw [t'.length_msgs, List.length_map, List.length_range]; rfl)).2
      exact (List.cons.inj hlast).1
    change Oracle.Transcript.snoc
        (extractPcs P bits k (t'.mapIdx fun j msg => spongeStepRead m params shape wf j msg c))
        (extractStepPcsMsg P (extractBatchFn P (t'.mapIdx fun j msg => spongeStepRead m params shape wf j msg c))
          k (spongeStepRead m params shape wf (P.batches + k) msg c))
        (spongeChalCast P bits chal) =
      Oracle.Transcript.snoc
        ((spongeToGrindTranscript (P := P) (bits := bits) (M' := Compiled.Msg K D P.batches)
            (fun j => view m params shape (a.messages params shape j)) k t').mapIdx
          fun j msg => P.read j msg c)
        (P.read k (view m params shape (a.messages params shape k)) c)
        (spongeChalCast P bits chal)
    rw [extractPcs_mapIdx_eq a c k t' hmsgs']
    congr 1
    cases k with
    | zero =>
      subst hmsg_eq
      change extractStepPcsMsg P (extractBatchFn P _) 0
          (spongeStepRead m params shape wf P.batches (a.spongeMessages params shape P.batches) c) =
        P.read 0 (view m params shape (a.messages params shape 0)) c
      have hread0 : spongeStepRead m params shape wf P.batches
          (a.spongeMessages params shape P.batches) c =
          .round0Meta (view m params shape (a.spongeMessages params shape P.batches)).points
            (view m params shape (a.spongeMessages params shape P.batches)).values := by
        unfold spongeStepRead
        dsimp only
        rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hread0]
      change assembleClaims P (extractBatchFn P _)
          (view m params shape (a.spongeMessages params shape P.batches)).points
          (view m params shape (a.spongeMessages params shape P.batches)).values =
        assembleClaims P (fun b => c ((view m params shape (a.messages params shape 0)).inputRoots b))
          (view m params shape (a.messages params shape 0)).points
          (view m params shape (a.messages params shape 0)).values
      congr 1
      · funext b
        have hb : b.val < P.batches := b.isLt
        have hm_map : ∀ {i : ℕ} (u : Oracle.Transcript (RawMsg F EF D) (SpongeChal P bits) i)
            (g : ℕ → RawMsg F EF D → StepMsg K P.numClaims),
            (u.mapIdx g).msgs = u.msgs.zipIdx.map fun p => g p.2 p.1 := by
          intro i u g
          induction u with
          | nil => rfl
          | snoc u _ _ ihu =>
            simp only [Transcript.mapIdx_snoc, Transcript.msgs_snoc, ihu, List.zipIdx_append,
              List.map_append, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
              u.length_msgs, Nat.zero_add]
        have hget : (t'.mapIdx fun j msg => spongeStepRead m params shape wf j msg c).msgs[b.val]? =
            some (spongeStepRead m params shape wf b.val (a.spongeMessages params shape b.val) c) := by
          rw [hm_map, List.getElem?_map, List.getElem?_zipIdx, hmsgs', List.getElem?_map,
            List.getElem?_range (by omega)]
          simp
        have hsr : spongeStepRead m params shape wf b.val (a.spongeMessages params shape b.val) c =
            .batchRoot (c (a.commitments.getD b.val default)) := by
          unfold spongeStepRead
          dsimp only
          rw [ite_eq_left (show b.val < (modelParams m params shape wf).batches from hb)]
          have hsm : a.spongeMessages params shape b.val = [.digest (a.commitments.getD b.val default)] := by
            unfold Attempt.spongeMessages
            rw [ite_eq_left (show b.val < shape.length from hb)]
          rw [hsm]
          rfl
        unfold extractBatchFn
        rw [hget, hsr]
        dsimp only
        have hfirst : (view m params shape (a.messages params shape 0)).inputRoots b =
            a.commitments.getD b.val default := by
          have hm0 : a.messages params shape 0 =
              firstMessage (F := F) a.commitments a.points a.values := rfl
          change (digestsIn (a.messages params shape 0)).getD b.val default =
            a.commitments.getD b.val default
          rw [hm0]
          have hdig_append : ∀ l₁ l₂ : List (Observation F EF D),
              digestsIn (l₁ ++ l₂) = digestsIn l₁ ++ digestsIn l₂ := fun l₁ l₂ => by
            simp [digestsIn, List.filterMap_append]
          have hpts : digestsIn (a.points.toList.map (Observation.ext (F := F) (D := D))) = [] := by
            unfold digestsIn; induction a.points.toList <;> simp [*]
          have hvals : digestsIn (a.values.toList.map (Observation.ext (F := F) (D := D))) = [] := by
            unfold digestsIn; induction a.values.toList <;> simp [*]
          have hdigs : digestsIn (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) =
              a.commitments.toList := by
            unfold digestsIn; induction a.commitments.toList <;> simp [*]
          rw [firstMessage, hdig_append, hdig_append, hdigs, hpts, hvals,
            List.append_nil, List.append_nil]
          by_cases hlt : b.val < a.commitments.size <;>
            simp [Array.getD, List.getD_eq_getElem?_getD, hlt]
        rw [hfirst]
      · have hexts : extsIn m (a.spongeMessages params shape P.batches) =
            extsIn m (a.messages params shape 0) := by
          have hs : a.spongeMessages params shape P.batches =
              a.points.toList.map .ext ++ a.values.toList.map .ext := by
            change a.spongeMessages params shape shape.length = _
            unfold Attempt.spongeMessages
            rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
          have hm0 : a.messages params shape 0 =
              firstMessage (F := F) a.commitments a.points a.values := rfl
          have hext_append : ∀ l₁ l₂ : List (Observation F EF D),
              extsIn m (l₁ ++ l₂) = extsIn m l₁ ++ extsIn m l₂ := fun l₁ l₂ => by
            simp [extsIn, List.filterMap_append]
          have hdigs : extsIn m (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) = [] := by
            unfold extsIn; induction a.commitments.toList <;> simp [*]
          rw [hs, hm0, firstMessage, hext_append, hext_append, hext_append, hdigs, List.nil_append]
        simp [view, hexts]
      · have hexts : extsIn m (a.spongeMessages params shape P.batches) =
            extsIn m (a.messages params shape 0) := by
          have hs : a.spongeMessages params shape P.batches =
              a.points.toList.map .ext ++ a.values.toList.map .ext := by
            change a.spongeMessages params shape shape.length = _
            unfold Attempt.spongeMessages
            rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
          have hm0 : a.messages params shape 0 =
              firstMessage (F := F) a.commitments a.points a.values := rfl
          have hext_append : ∀ l₁ l₂ : List (Observation F EF D),
              extsIn m (l₁ ++ l₂) = extsIn m l₁ ++ extsIn m l₂ := fun l₁ l₂ => by
            simp [extsIn, List.filterMap_append]
          have hdigs : extsIn m (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) = [] := by
            unfold extsIn; induction a.commitments.toList <;> simp [*]
          rw [hs, hm0, firstMessage, hext_append, hext_append, hext_append, hdigs, List.nil_append]
        simp [view, hexts]
    | succ k' =>
      subst hmsg_eq
      have hgt : ¬ (P.batches + (k' + 1) < P.batches) := by omega
      have hne : P.batches + (k' + 1) ≠ P.batches := by omega
      have hsub : P.batches + (k' + 1) - P.batches = k' + 1 := Nat.add_sub_cancel_left _ _
      have hmsg' : a.spongeMessages params shape (P.batches + (k' + 1)) =
          a.messages params shape (k' + 1) := by
        unfold Attempt.spongeMessages
        have hb : P.batches = shape.length := rfl
        rw [hb, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rw [hmsg']
      unfold spongeStepRead
      dsimp only
      rw [ite_eq_right hgt, ite_eq_right hne, hsub]
      rfl

/-- **Soundness of executable `Fri.verify` under incremental sponge chaining (`c = 3 / 2`).**
Whatever the adversary (making at most `Q` oracle queries), the probability that
`Fri.verify` accepts under the incremental sponge challenger (`spongeAccepts`)
while the committed claims fail is at most
`N * εmax + 3 * N ^ 2 / (2 * Fintype.card D)`,
where `N = Q + (batches + rounds + 2) + P.verifierQueries`. -/
theorem soundness_sponge (s₀ : D) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ (modelParams m params shape wf).rounds,
      CurveMCA ((twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n j).image ((modelParams m params shape wf).shift * ·))
        (2 ^ ((modelParams m params shape wf).rounds - j) *
          (modelParams m params shape wf).finalDegree)
        ((modelParams m params shape wf).numClaims j) θ (εα j))
    (hstep : ∀ i < (modelParams m params shape wf).rounds,
      StepMCA (twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n i)
        (twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n (i + 1))
        (2 ^ ((modelParams m params shape wf).rounds - (i + 1)) *
          (modelParams m params shape wf).finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range ((modelParams m params shape wf).rounds + 1), εα j) ≤ εmax)
    (hβ : ∀ i < (modelParams m params shape wf).rounds,
      εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts m params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment m params shape wf s₀ adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        3 * ((Q : ℝ) + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) ^ 2 / (2 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let bits := powBits params shape
  have hε0 : 0 ≤ εmax := (div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq
  have hε : ∀ i < P.batches + (P.rounds + 2),
      (if i < P.batches then 0
        else roundError P.rounds εα εβ θ P.queries (i - P.batches) / 2 ^ bits (i - P.batches)) ≤ εmax := by
    intro i hi
    split_ifs with hlt
    · exact hε0
    · rcases hsub : i - P.batches with _ | k
      · rw [PcsRbr.roundError_zero, show bits 0 = 0 from powBits_zero params shape, pow_zero, div_one]
        exact hα
      · by_cases hk : k < P.rounds
        · rw [PcsRbr.roundError_succ_of_lt hk,
            show bits (k + 1) = params.commitPowBits from powBits_succ_of_lt params shape hk]
          exact hβ k hk
        · obtain rfl : k = P.rounds := by omega
          rw [PcsRbr.roundError_last,
            show bits (P.rounds + 1) = params.queryPowBits from powBits_last params shape]
          exact hq
  have hbound := prob_spongeExperiment_bind_committedRow_le (s₀ := s₀)
    (r := P.batches + (P.rounds + 2))
    (rbrSound_sponge P bits hθ hmca hstep) hε hε0 (spongeDoomed_nil P bits θ)
    (stepDigestsOf := spongeStepDigests (F := F) (EF := EF) P) (M := 1) (by decide)
    (fun i _ msg => length_spongeStepDigests_le_one P i msg)
    (read := spongeStepRead m params shape wf)
    (fun j msg c c' hc => spongeStepRead_congr m params shape wf j msg c c' hc)
    hadv (fun a => (attempt a).spongeMessages params shape)
    (rest := fun out =>
      (spongeVerify m params shape wf (attempt out.1) out.2).bind fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (queryBound_spongeVerify m params shape wf (attempt out.1) out.2).bind (m := 0) fun _ =>
      queryBound_pure _ _)
    (E := fun res l =>
      (∃ f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          spongeAccepts m params shape wf s₀ f (attempt res.1) = true) ∧
      ClaimsFail P.ldt P.shift θ
        (P.claims (view m params shape (firstMessage (attempt res.1).commitments
          (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
    fun out l res l' hexp hrun ⟨⟨f, hf, hacc⟩, hfail⟩ hno => by
      obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      have hcomm : (attempt out.1).commitments.size = shape.length := by
        unfold spongeAccepts Fri.verify Fri.shapeOk at hacc
        simp only [Bool.and_eq_true, beq_iff_eq] at hacc
        exact hacc.1.1.1.1.1.1.1.1.1.1.2
      have hacc_free := accepts_liftSpongeOracle_of_spongeAccepts m params shape wf s₀ f
        (attempt out.1) hacc
      have hmodel_true : (P.verifyGrindView bits (view m params shape)
          (modelProof m params shape (attempt out.1).proof)
          (fsTranscript (liftSpongeOracle P bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))).run
          (liftSpongeOracle P bits s₀ f) = true :=
        run_model_of_accepts m params shape wf
          (liftSpongeOracle P bits s₀ f) (attempt out.1) hacc_free
      have hts : out.2 = spongeTranscript f s₀ ((attempt out.1).spongeMessages params shape)
          (P.batches + (P.rounds + 2)) := by
        have h1 := eq_spongeTranscript_of_outcome_spongeExperiment hexp hver.prefix f
        rwa [toFun_eq_self hf] at h1
      let tg := spongeToGrindTranscript (P := P) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => view m params shape ((attempt out.1).messages params shape j)) (P.rounds + 2) out.2.1
      have htg_eq : tg = (fsTranscript (liftSpongeOracle P bits s₀ f)
          ((attempt out.1).messages params shape) (P.rounds + 2)).mapIdx
          (fun _ msg => (view m params shape msg : Compiled.Msg K D P.batches)) := by
        dsimp only [tg]
        rw [hts]
        exact spongeToGrindTranscript_eq_fsTranscript m params shape wf s₀ f (attempt out.1) hcomm
          (P.rounds + 2)
      have hb_true : b = true := by
        have hrun_f : (spongeVerify m params shape wf (attempt out.1) out.2).run f = b := by
          have := hver.run_toFun f
          rwa [toFun_eq_self hf] at this
        rw [← hrun_f]
        unfold spongeVerify
        dsimp only
        obtain ⟨hpow_fs, hvw⟩ :=
          (P.run_verifyGrindView bits (view m params shape) (liftSpongeOracle P bits s₀ f) _ _).mp
            hmodel_true
        have hpow_tg : PowPasses tg := by
          rw [htg_eq]
          exact (PcsRbr.powPasses_mapIdx _ _).mpr hpow_fs
        change (if PowPasses tg then
            mapHashToSponge (M := RawMsg F EF D) (C := SpongeChal P bits)
              (P.verifyWith (M := Empty) (C := fun _ => PUnit)
                (modelProof m params shape (attempt out.1).proof) (Compiled.msgAt (ungrind tg))
                (alphaOf (ungrind tg)) (betasOf (ungrind tg))
                (fun k => P.indexOf (queriesOf (ungrind tg) k)))
          else .pure false).run f = true
        rw [ite_eq_left hpow_tg, run_mapHashToSponge]
        have hrun_vw := P.run_verifyWith (projHashFun f) (modelProof m params shape (attempt out.1).proof)
          (Compiled.msgAt (ungrind tg)) (alphaOf (ungrind tg)) (betasOf (ungrind tg))
          (fun k => P.indexOf (queriesOf (ungrind tg) k))
        have hrun_fs := P.run_verifyWith (liftSpongeOracle P bits s₀ f)
          (modelProof m params shape (attempt out.1).proof)
          (fun j => view m params shape (Compiled.msgAt (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))) j))
          (alphaOf (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))))
          (betasOf (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))))
          (fun k => P.indexOf (queriesOf (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))) k))
        rw [hrun_vw]
        rw [hrun_fs] at hvw
        have hhash_eq : hasherOf (projHashFun f) = hasherOf (liftSpongeOracle P bits s₀ f) := rfl
        let vP : RawMsg F EF D → Compiled.Msg K D P.batches := view m params shape
        have htu_eq : ungrind tg = (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))).mapIdx
            (fun _ msg => vP msg) := by
          rw [htg_eq]
          exact PcsRbr.ungrind_mapIdx _ _
        have hmsgs_map : ∀ {M₁ M₂ : Type} {C : ℕ → Type} {n : ℕ}
            (u : Oracle.Transcript M₁ C n) (g : M₁ → M₂),
            (u.mapIdx fun _ msg => g msg).msgs = u.msgs.map g := by
          intro M₁ M₂ C n u g
          induction u with
          | nil => rfl
          | snoc u _ _ ihu => simp [Transcript.mapIdx_snoc, Transcript.msgs_snoc, ihu]
        have hmsgAt_map : ∀ {M₁ M₂ : Type} {C : ℕ → Type} {n : ℕ}
            (u : Oracle.Transcript M₁ C (n + 1)) (g : M₁ → M₂) (j : ℕ),
            Compiled.msgAt (u.mapIdx fun _ msg => g msg) j = g (Compiled.msgAt u j) := by
          intro M₁ M₂ C n u g j
          cases u with
          | snoc u' msg ch =>
            simp only [Transcript.mapIdx_snoc, Compiled.msgAt, hmsgs_map,
              List.getD_eq_getElem?_getD, List.getElem?_map]
            cases u'.msgs[j]? <;> rfl
        have hmsg_eq : Compiled.msgAt (ungrind tg) =
            fun j => vP (Compiled.msgAt (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) j) := by
          funext j
          rw [htu_eq]
          exact hmsgAt_map _ vP j
        have hα_eq : alphaOf (ungrind tg) =
            alphaOf (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.alphaOf_mapIdx _ _
        have hβ_eq : betasOf (ungrind tg) =
            betasOf (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.betasOf_mapIdx _ _
        have hq_eq : queriesOf (ungrind tg) =
            queriesOf (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.queriesOf_mapIdx _ _
        rw [hhash_eq, hmsg_eq, hα_eq, hβ_eq, hq_eq]
        exact hvw
      subst hb_true
      unfold spongeVerify at hver
      dsimp only at hver
      split_ifs at hver with hpow_tg
      · have hproj_out := outcome_projHashLog hver
        have hnocol_proj : ¬ LogCollision hashObs (projHashLog l') := fun hc =>
          not_logCollision_sponge_of_not_jointHit hno (logCollision_projHashLog_iff.mp hc)
        have hacc_pcs := P.accepts_of_outcome_verifyWith (ungrind tg) hproj_out hnocol_proj
        rw [committedRow_projHashLog] at hacc_pcs
        obtain ⟨_, -, hder⟩ := outcome_spongeExperiment hexp
        obtain ⟨_, hmsgs⟩ := outcome_spongeDerive_supports hder
        have hextr : extractPcs P bits (P.rounds + 2)
            (out.2.1.mapIdx fun j msg => spongeStepRead m params shape wf j msg (spongeCommittedRow l')) =
            tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l') :=
          extractPcs_mapIdx_eq m params shape wf (attempt out.1)
            (spongeCommittedRow l') (P.rounds + 2) out.2.1 hmsgs
        rw [spongeDoomed_add_succ P bits θ (P.rounds + 1), hextr]
        have hungrind_tg : ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l')) =
            (ungrind tg).mapIdx fun j msg => P.read j msg (spongeCommittedRow l') :=
          PcsRbr.ungrind_mapIdx _ tg
        refine PcsRbr.not_grindDoomed_of_accepts _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow_tg) ?_ ?_
        · let vP : RawMsg F EF D → Compiled.Msg K D P.batches := view m params shape
          have h0 : (ungrind tg).msgs[0]? =
              some (vP ((attempt out.1).messages params shape 0)) := by
            have hu : ungrind tg = (ungrind (fsTranscript (liftSpongeOracle P bits s₀ f)
                ((attempt out.1).messages params shape) (P.rounds + 2))).mapIdx
                (fun _ msg => vP msg) := by
              rw [htg_eq]
              exact PcsRbr.ungrind_mapIdx _ _
            have hmsgs_map : ∀ {M₁ M₂ : Type} {C : ℕ → Type} {n : ℕ}
                (u : Oracle.Transcript M₁ C n) (g : M₁ → M₂),
                (u.mapIdx fun _ msg => g msg).msgs = u.msgs.map g := by
              intro M₁ M₂ C n u g
              induction u with
              | nil => rfl
              | snoc u _ _ ihu => simp [Transcript.mapIdx_snoc, Transcript.msgs_snoc, ihu]
            rw [hu, hmsgs_map _ vP, Compiled.msgs_ungrind, fsTranscript_msgs,
              List.getElem?_map, List.getElem?_map, List.getElem?_range (Nat.succ_pos _)]
            rfl
          change ClaimsFail P.ldt P.shift θ
            (PcsRbr.claimsOf (ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l'))))
          rw [hungrind_tg, PcsRbr.claimsOf_mapIdx _ (ungrind tg) h0]
          exact hfail
        · change Accepts P.ldt P.shift
            (ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l')))
          rw [hungrind_tg]
          exact hacc_pcs
      · exact absurd (outcome_pure.mp hver).1 (by simp)
  have hcast : ((Q : ℝ) + ((P.batches + (P.rounds + 2) : ℕ) : ℝ) + P.verifierQueries) =
      (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    push_cast; ring
  rw [hcast] at hbound
  exact hbound

/-- **Unconditional unique-decoding soundness of `Fri.verify` under incremental
sponge chaining (`c = 3 / 2`).** -/
theorem soundness_sponge_uniqueDecoding (s₀ : D)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts m params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift (1 - δ)
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment m params shape wf s₀ adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        3 * ((Q : ℝ) + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) ^ 2 / (2 * Fintype.card D) := by
  let P := modelParams m params shape wf
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hθ : 0 ≤ 1 - δ := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ params.logBlowup := by positivity
    linarith
  have hmca : ∀ j ≤ P.rounds,
      CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) (1 - δ)
        (((P.numClaims j - 1 : ℕ) : ℝ) * ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K) :=
    fun j hj => P.curveMCA_of_rate_of_curveCA (curveCA_udThreshold (F := K)) hn rfl hδ hrate hj _
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) (1 - δ)
        (((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K) :=
    fun i hi => P.stepMCA_of_rate_of_curveCA (curveCA_udThreshold (F := K)) hn rfl hδ hrate hi
  refine soundness_sponge m params shape wf s₀ hθ hmca hstep ?_ (fun _ _ => hβ) hq hadv attempt
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have hsum : (∑ j ∈ Finset.range (P.rounds + 1), ((P.numClaims j - 1 : ℕ) : ℝ)) ≤
      ((claimRefs params.logBlowup shape).length : ℝ) := by
    exact_mod_cast sum_numClaims_sub_one_le m params shape wf
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (by positivity)) (Nat.cast_nonneg _)).trans hα

/-- **Johnson-regime soundness of `Fri.verify` under incremental sponge chaining
(`c = 3 / 2`), assuming `CurveListCA K T`.** -/
theorem soundness_sponge_johnson (s₀ : D) {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA K T)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (T (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts m params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment m params shape wf s₀ adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        3 * ((Q : ℝ) + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) ^ 2 / (2 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let ρ : ℝ := (1 / 2 : ℝ) ^ params.logBlowup
  let LJ : ℝ := (θ - ρ) / (θ ^ 2 - ρ)
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hfinal : P.finalDegree = 2 ^ params.logFinalPolyLen := rfl
  have hLJ_nn : 0 ≤ LJ := by
    have hden : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
    have hnum : 0 ≤ θ - ρ := by nlinarith
    exact div_nonneg hnum hden.le
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hdeg_le : ∀ j ≤ P.rounds,
      ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
        ρ * ((twoAdicDomain P.ω P.n j).card : ℝ) := by
    intro j hj
    rw [hfinal, Compose.card_twoAdicDomain_eq_mul_degree hn P.prim hj]
    push_cast
    have h1 : ρ * (2 : ℝ) ^ params.logBlowup = 1 := by
      dsimp only [ρ]; rw [← mul_pow]; norm_num
    rw [← mul_assoc, h1, one_mul]
  have hcard_dom : ∀ j ≤ P.rounds, (twoAdicDomain P.ω P.n j).card = 2 ^ (P.n - j) :=
    fun j hj => card_twoAdicDomain P.prim (by omega)
  let εα : ℕ → ℝ := fun j =>
    ((P.numClaims j - 1 : ℕ) : ℝ) * (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  let εβ : ℕ → ℝ := fun _ =>
    (2 * cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hmca : ∀ j ≤ P.rounds,
      CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j) := by
    intro j hj
    by_cases hk : P.numClaims j ≤ 1
    · intro u
      refine ⟨∅, by simp only [Finset.card_empty, Nat.cast_zero]; dsimp only [εα]; positivity,
        fun α _ p hp B _ _ hagree => ?_⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
      · refine ⟨fun k => (h0 ▸ k).elim0, fun k => (h0 ▸ k).elim0, fun k => (h0 ▸ k).elim0⟩
      · refine ⟨fun _ => p, fun _ => hp, fun k x hx => ?_⟩
        have h := hagree x hx
        have hfin : ∀ (m : ℕ) (hm : m = 1) (k : Fin m) (u : Fin m → K → K),
            (∑ l : Fin m, α ^ l.val * u l x) = u k x := by
          rintro m rfl k u
          rw [Fin.sum_univ_one]
          have : k = 0 := Subsingleton.elim k 0
          subst this
          simp
        rw [hfin (P.numClaims j) h1 k u] at h
        exact h
    · have hk2 : 2 ≤ P.numClaims j := by omega
      have hcard_img : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card = 2 ^ (P.n - j) := by
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne), hcard_dom j hj]
      have hcard_le : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ P.n := by
        rw [hcard_img]
        exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n j)
      have hd_img : ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
          ρ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) := by
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
        exact hdeg_le j hj
      have hTj : (T ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card
          (2 ^ (P.rounds - j) * P.finalDegree)
          ⌈θ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ)⌉₊
          (P.numClaims j) : ℝ) ≤ ((P.numClaims j - 1 : ℕ) : ℝ) * cT := by
        rw [hcard_img, hfinal]
        push_cast
        exact hT j (P.numClaims j) hj hk2
      have hcurve := curveMCA_of_curveListCA_of_card_le hca
        ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j)
        hθ0 hθ1 hd_img hgap (by positivity) hTj hcard_le
      refine ProximityGap.curveMCA_mono hcurve le_rfl ?_
      dsimp only [εα, LJ, ρ]
      exact le_of_eq (by ring)
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i) := by
    intro i hi
    have hi1 : i + 1 ≤ P.rounds := hi
    have hn1 : 1 ≤ P.n := by omega
    have hcard_i1 : (twoAdicDomain P.ω P.n (i + 1)).card = 2 ^ (P.n - (i + 1)) :=
      hcard_dom (i + 1) hi1
    have hcard_le : ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ (2 : ℝ) ^ (P.n - 1) := by
      rw [hcard_i1]
      exact_mod_cast Nat.pow_le_pow_right two_pos (by omega)
    have hTi : (T (twoAdicDomain P.ω P.n (i + 1)).card
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
        ⌈θ * ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ)⌉₊ 3 : ℝ) ≤ 2 * cT := by
      rw [hcard_i1, hfinal]
      push_cast
      have h := hT (i + 1) 3 hi1 (by omega)
      norm_num at h
      exact h
    have hst := stepMCA_of_curveListCA_of_card_le hca (P.ldt.step i hi)
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
      hθ0 hθ1 (hdeg_le (i + 1) hi1) hgap (by positivity) hTi hcard_le
    have h2pow : 2 * (2 : ℝ) ^ (P.n - 1) = (2 : ℝ) ^ P.n := by
      conv_rhs => rw [← Nat.sub_add_cancel hn1, pow_succ']
    have heq : (2 * cT + 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1)))) / Fintype.card K = εβ i := by
      dsimp only [εβ]
      have : 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1))) =
          LJ * ((1 - θ) * (2 * (2 : ℝ) ^ (P.n - 1))) := by ring
      rw [this, h2pow]
    rwa [heq] at hst
  refine soundness_sponge m params shape wf s₀ hθ0.le hmca hstep ?_ (fun _ _ => hβ) hq hadv attempt
  dsimp only [εα]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have hsum : (∑ j ∈ Finset.range (P.rounds + 1), ((P.numClaims j - 1 : ℕ) : ℝ)) ≤
      ((claimRefs params.logBlowup shape).length : ℝ) := by
    exact_mod_cast sum_numClaims_sub_one_le m params shape wf
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (by positivity)) (Nat.cast_nonneg _)).trans hα

end ExecSponge

end CertiFri.Exec

/-! ## Concrete `GoldilocksExt3` instantiations (32B `BLAKE3-256` & 64B `BLAKE2b-512`, classical ROM) -/

namespace CertiFri.P3.Exec

open CertiFri.Exec CertiFri.Fri CertiFri.Oracle CertiFri.Oracle.OracleComp CertiFri.PcsRbr

/-- **32-byte `BLAKE3-256` incremental-sponge unconditional UD soundness over `GoldilocksExt3`**
(production 128-bit **classical** instantiation).
Shrinks the BCS collision prefactor from `7.75` to `3 / 2` (`126.52b → 127.71b`
with zero prover cost), giving collision term `3 * N ^ 2 / (2 * 2 ^ 256)`. -/
theorem goldilocksExt3_soundness_sponge_uniqueDecoding
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (1 - δ)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * (2 : ℝ) ^ 256) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  have hcardD : (Fintype.card Digest : ℝ) = (2 : ℝ) ^ 256 := by
    rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hcardD] using soundness_sponge_uniqueDecoding goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hmax) s₀ hheight hδ hrate
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

/-- **64-byte (512-bit) RFC 7693 `BLAKE2b-512` unconditional UD soundness over `GoldilocksExt3`**
in the **classical** random oracle model (`|Digest64| = 2 ^ 512`).
Gives `3 * N ^ 2 / (2 * 2 ^ 512)` classical BCS collision resistance (`255.71b`
classical threshold, keeping the classical collision term `≤ N / (4 * 2 ^ 128)`
for `N ≤ 2 ^ 128`). **Scope note:** a 64-byte digest provides
classical collision resistance in the classical ROM, **not** certified 128-bit
post-quantum protocol soundness (QROM Fiat–Shamir and Grover search against FRI
queries/PoW are not formalized here; the `DigestCard.lean` lemmas
`digest64_bht_quantum_collision_at_128`, `digest64_bht_quantum_collision_at_170`,
`digest64_cns_quantum_collision_at_204`, `digest64_grover_preimage` are pure
arithmetic inequalities on `|Digest64| = 2 ^ 512`). -/
theorem goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest64)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (1 - δ)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * (2 : ℝ) ^ 512) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  have hcardD : (Fintype.card Digest64 : ℝ) = (2 : ℝ) ^ 512 := by
    rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hcardD] using soundness_sponge_uniqueDecoding goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hmax) s₀ hheight hδ hrate
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

/-- Arithmetic fact: Goldilocks `order ^ 3 ≥ 2 ^ 191` (`p = 2^64 - 2^32 + 1`, so
`p^3 ≈ 2^192`, strictly above `2^191`). -/
theorem two_pow_191_le_goldilocks_cube :
    (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := by
  have hord : (2 : ℝ) ^ 64 * (9 / 10) ≤ (Goldilocks.order : ℝ) := by
    unfold Goldilocks.order
    norm_num
  have hpow : (2 : ℝ) ^ 191 ≤ ((2 : ℝ) ^ 64 * (9 / 10)) ^ 3 := by
    rw [mul_pow, ← pow_mul]
    have h192 : (2 : ℝ) ^ (64 * 3) = 2 * (2 : ℝ) ^ 191 := by
      rw [show (64 * 3 : ℕ) = 191 + 1 by decide, pow_succ']
    rw [h192]
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ 191 := by positivity
    nlinarith [show (1 : ℝ) ≤ 2 * (9 / 10 : ℝ) ^ 3 by norm_num]
  exact hpow.trans (pow_le_pow_left₀ (by positivity) hord 3)

/-- Concrete UD query error check for `(logBlowup = 2, numQueries = 160, queryPowBits = 20)`:
`(5 / 8) ^ 160 / 2 ^ 20 ≤ 3 / (4 * 2 ^ 128)` (`128.49` bits of unconditional UD query soundness). -/
theorem ud_160_pow20_le_three_quarters_128 :
    ((5 / 8 : ℝ) ^ 160) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have h5 : (5 : ℕ) ^ 160 * 4 ≤ 3 * 2 ^ 372 := by
    have h40 : (5 : ℕ) ^ 40 * 100 ≤ 92 * 2 ^ 93 := by norm_num
    have hpow : ((5 : ℕ) ^ 40 * 100) ^ 4 ≤ (92 * 2 ^ 93) ^ 4 :=
      Nat.pow_le_pow_left h40 4
    have h92 : (92 : ℕ) ^ 4 * 4 ≤ 3 * 100 ^ 4 := by norm_num
    have hmul : (5 : ℕ) ^ 160 * 100 ^ 4 * 4 ≤ 3 * 100 ^ 4 * 2 ^ 372 := by
      calc (5 : ℕ) ^ 160 * 100 ^ 4 * 4
          = ((5 ^ 40 * 100) ^ 4) * 4 := by rw [mul_pow, ← pow_mul]
        _ ≤ ((92 * 2 ^ 93) ^ 4) * 4 := Nat.mul_le_mul_right 4 hpow
        _ = (92 ^ 4 * 4) * 2 ^ 372 := by rw [mul_pow, ← pow_mul, mul_right_comm]
        _ ≤ (3 * 100 ^ 4) * 2 ^ 372 := Nat.mul_le_mul_right _ h92
    have hpos100 : 0 < (100 : ℕ) ^ 4 := by decide
    refine Nat.le_of_mul_le_mul_left ?_ hpos100
    calc (100 : ℕ) ^ 4 * (5 ^ 160 * 4) = 5 ^ 160 * 100 ^ 4 * 4 := by
            rw [← mul_assoc, mul_comm (100 ^ 4) (5 ^ 160)]
      _ ≤ 3 * 100 ^ 4 * 2 ^ 372 := hmul
      _ = 100 ^ 4 * (3 * 2 ^ 372) := by
            rw [mul_comm 3 (100 ^ 4), mul_assoc]
  have h5r : (5 : ℝ) ^ 160 * 4 ≤ 3 * (2 : ℝ) ^ 372 := by exact_mod_cast h5
  have h8 : ((5 / 8 : ℝ) ^ 160) / (2 : ℝ) ^ 20 = (5 : ℝ) ^ 160 / (2 : ℝ) ^ 500 := by
    rw [div_pow, div_div, show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_mul, ← pow_add]
  have h500 : (2 : ℝ) ^ 500 = (2 : ℝ) ^ 372 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  rw [h8, h500]
  have hpos372 : (0 : ℝ) < (2 : ℝ) ^ 372 := pow_pos (by norm_num) 372
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  rw [div_le_div_iff₀ (mul_pos hpos372 hpos128) hpos128]
  have hmul : (5 : ℝ) ^ 160 * 4 * (2 : ℝ) ^ 128 ≤ (3 * (2 : ℝ) ^ 372) * (2 : ℝ) ^ 128 :=
    mul_le_mul_of_nonneg_right h5r hpos128.le
  have h1 : (4 : ℝ) * ((5 : ℝ) ^ 160 * (2 : ℝ) ^ 128) ≤
      (4 : ℝ) * ((3 / 4 : ℝ) * ((2 : ℝ) ^ 372 * (2 : ℝ) ^ 128)) := by
    calc (4 : ℝ) * ((5 : ℝ) ^ 160 * (2 : ℝ) ^ 128)
        = (5 : ℝ) ^ 160 * 4 * (2 : ℝ) ^ 128 := by rw [← mul_assoc, mul_comm (4 : ℝ)]
      _ ≤ (3 * (2 : ℝ) ^ 372) * (2 : ℝ) ^ 128 := hmul
      _ = (4 : ℝ) * ((3 / 4 : ℝ) * ((2 : ℝ) ^ 372 * (2 : ℝ) ^ 128)) := by
          rw [mul_assoc, ← mul_assoc (4 : ℝ) (3 / 4 : ℝ), show (4 : ℝ) * (3 / 4 : ℝ) = 3 by norm_num]
  exact le_of_mul_le_mul_left h1 (by norm_num)

/-- **Literal `≤ N / 2 ^ 128` unconditional unique-decoding soundness** for
`GoldilocksExt3` with 64-byte RFC 7693 `BLAKE2b-512` (`Digest64`, 512-bit
internal state), incremental sponge chaining (`c = 3 / 2`), and
`(logBlowup = 2, numQueries = 160, commitPowBits = 0, queryPowBits = 20)`.
Holds for EVERY query budget `N ≤ 2 ^ 128` whenever
`claimRefs.length * 2 ^ logMaxHeight ≤ 2 ^ 60`! -/
theorem goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : params.numQueries = 160) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 60)
    (s₀ : Digest64)
    {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (5 / 8)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  intro wf P N
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have h1 : (11 / 8 : ℝ) * (2 : ℝ) ^ 60 / (2 : ℝ) ^ 191 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
    have h63 : (2 : ℝ) ^ 63 = 8 * (2 : ℝ) ^ 60 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_add]
    rw [h191e, h63, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ 60 * (2 : ℝ) ^ 128 by positivity]
  have hεα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
      ((1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
      ((Goldilocks.order : ℝ) ^ 3) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hcr : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤ (2 : ℝ) ^ 60 := by
      exact_mod_cast hclaims
    have hnum : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤
        (11 / 8 : ℝ) * (2 : ℝ) ^ 60 := by nlinarith
    exact (div_le_div₀ (by positivity) hnum (by positivity) h191).trans h1
  have hεβ : ((1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
      ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have h2n : (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤ (2 : ℝ) ^ 32 := by
      exact_mod_cast Nat.pow_le_pow_right two_pos hmax
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ params.commitPowBits := by
      exact_mod_cast Nat.one_le_pow params.commitPowBits 2 two_pos
    have hnum : (1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤
        (11 / 8 : ℝ) * (2 : ℝ) ^ 60 := by
      have : (2 : ℝ) ^ 32 ≤ (2 : ℝ) ^ 60 := by
        exact_mod_cast Nat.pow_le_pow_right two_pos (by decide)
      nlinarith
    exact (div_le_self (by positivity) hpow1).trans
      ((div_le_div₀ (by positivity) hnum (by positivity) h191).trans h1)
  have hεq : (1 - (3 / 8 : ℝ)) ^ params.numQueries / 2 ^ params.queryPowBits ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [hqn, hqpow, show (1 - 3 / 8 : ℝ) = 5 / 8 by norm_num]
    exact ud_160_pow20_le_three_quarters_128
  have hrate : 2 * (3 / 8 : ℝ) + (1 / 2) ^ params.logBlowup ≤ 1 := by
    rw [hbl]; norm_num
  have hmain := goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding params shape hmax hheight s₀
    (δ := 3 / 8) (by norm_num) hrate (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128) hεα hεβ hεq hadv attempt
  dsimp only at hmain
  have h58 : (1 - (3 / 8 : ℝ)) = 5 / 8 := by norm_num
  rw [h58] at hmain
  have hcol := digest64_sponge_collision_le_quarter_128 (N := N) hN
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at hcol
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rw [← hNcast] at hmain
  refine hmain.trans ?_
  calc (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add le_rfl hcol
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-- Concrete Johnson query error check for `(logBlowup = 2, numQueries ≥ 118, queryPowBits = 20)`
at agreement `θ = 65 / 128 = √(1/4) + 1/128`:
`(65 / 128) ^ q / 2 ^ 20 ≤ 3 / (4 * 2 ^ 128)` (`≥ 135.3` bits of query soundness!). -/
theorem johnson_ge_118_pow20_le_three_quarters_128 {q : ℕ} (hq : 118 ≤ q) :
    ((65 / 128 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono : (65 / 128 : ℝ) ^ q ≤ (65 / 128 : ℝ) ^ 118 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have h65 : (65 : ℕ) ^ 118 * 4 ≤ 3 * 2 ^ 718 := by
    have h20 : (65 : ℕ) ^ 20 ≤ 2 ^ 121 := by norm_num
    have h9 : (65 : ℕ) ^ 9 ≤ 2 ^ 55 := by norm_num
    have h118 : (65 : ℕ) ^ 118 = (65 ^ 20) ^ 5 * (65 ^ 9) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
    have hpow : (65 : ℕ) ^ 118 ≤ (2 ^ 121) ^ 5 * (2 ^ 55) ^ 2 := by
      rw [h118]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left h20 5) (Nat.pow_le_pow_left h9 2)
    have hexp : 121 * 5 + 55 * 2 + 2 = 717 := by decide
    have h4 : (4 : ℕ) = 2 ^ 2 := by decide
    have hpow2 : ((2 : ℕ) ^ 121) ^ 5 * ((2 : ℕ) ^ 55) ^ 2 * 4 = 2 ^ 717 := by
      rw [← pow_mul, ← pow_mul, ← pow_add, h4, ← pow_add, hexp]
    calc (65 : ℕ) ^ 118 * 4
        ≤ ((2 ^ 121) ^ 5 * (2 ^ 55) ^ 2) * 4 := Nat.mul_le_mul_right 4 hpow
      _ = 2 ^ 717 := hpow2
      _ ≤ 3 * 2 ^ 718 := by
          have hstep : ∀ (a n m : ℕ), 0 < a → m = n + 1 → a ^ n ≤ a ^ m := by
            rintro a n _ ha rfl
            rw [pow_succ]
            exact Nat.le_mul_of_pos_right _ ha
          have h1 : (2 : ℕ) ^ 717 ≤ 2 ^ 718 := hstep 2 717 718 (by omega) rfl
          have h2 : (2 : ℕ) ^ 718 ≤ 3 * 2 ^ 718 := Nat.le_mul_of_pos_left _ (by omega)
          exact h1.trans h2
  have h65r : (65 : ℝ) ^ 118 * 4 ≤ 3 * (2 : ℝ) ^ 718 := by exact_mod_cast h65
  have h128 : ((65 / 128 : ℝ) ^ 118) / (2 : ℝ) ^ 20 = (65 : ℝ) ^ 118 / (2 : ℝ) ^ 846 := by
    rw [div_pow, div_div, show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num, ← pow_mul, ← pow_add]
  have h846 : (2 : ℝ) ^ 846 = (2 : ℝ) ^ 718 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  have h118 : ((65 / 128 : ℝ) ^ 118) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [h128, h846]
    have hpos718 : (0 : ℝ) < (2 : ℝ) ^ 718 := pow_pos (by norm_num) 718
    have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
    rw [div_le_div_iff₀ (mul_pos hpos718 hpos128) hpos128]
    have hmul : (65 : ℝ) ^ 118 * 4 * (2 : ℝ) ^ 128 ≤ (3 * (2 : ℝ) ^ 718) * (2 : ℝ) ^ 128 :=
      mul_le_mul_of_nonneg_right h65r hpos128.le
    have h1 : (4 : ℝ) * ((65 : ℝ) ^ 118 * (2 : ℝ) ^ 128) ≤
        (4 : ℝ) * ((3 / 4 : ℝ) * ((2 : ℝ) ^ 718 * (2 : ℝ) ^ 128)) := by
      calc (4 : ℝ) * ((65 : ℝ) ^ 118 * (2 : ℝ) ^ 128)
          = (65 : ℝ) ^ 118 * 4 * (2 : ℝ) ^ 128 := by rw [← mul_assoc, mul_comm (4 : ℝ)]
        _ ≤ (3 * (2 : ℝ) ^ 718) * (2 : ℝ) ^ 128 := hmul
        _ = (4 : ℝ) * ((3 / 4 : ℝ) * ((2 : ℝ) ^ 718 * (2 : ℝ) ^ 128)) := by
            rw [mul_assoc, ← mul_assoc (4 : ℝ) (3 / 4 : ℝ), show (4 : ℝ) * (3 / 4 : ℝ) = 3 by norm_num]
    exact le_of_mul_le_mul_left h1 (by norm_num)
  exact (div_le_div_of_nonneg_right hmono (by positivity)).trans h118

/-- **64-byte RFC 7693 `BLAKE2b-512` Johnson-regime soundness over `GoldilocksExt3` (`c = 3 / 2`).** -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest64)
    {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA Fp3Model T)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ Fri.numRounds params shape → 2 ≤ k →
      (T (2 ^ (Fri.logMaxHeight params.logBlowup shape - j))
        (2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (Fri.logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape)) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape)) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift θ
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * (2 : ℝ) ^ 512) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  have hcardD : (Fintype.card Digest64 : ℝ) = (2 : ℝ) ^ 512 := by
    rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hcardD] using soundness_sponge_johnson goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hmax) s₀ hca hheight hθ0 hθ1 hgap hcT0 hT
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

/-- **Literal `≤ N / 2 ^ 128` Johnson-regime soundness** for `GoldilocksExt3`
with 64-byte RFC 7693 `BLAKE2b-512` (`Digest64`), incremental sponge chaining (`c = 3 / 2`),
and `(logBlowup = 2, numQueries ≥ 118, commitPowBits = 0, queryPowBits = 20)`
(covering `q = 118..128`!), conditional on `CurveListCA Fp3Model T`. Holds for
EVERY query budget `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson_128
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 118 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest64)
    {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA Fp3Model T)
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
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (65 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  intro wf P N
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have hLJ : ((65 / 128 : ℝ) - (1 / 2 : ℝ) ^ params.logBlowup) /
      ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup) * (1 - (65 / 128 : ℝ)) ≤ 17 := by
    rw [hbl]
    norm_num
  have h62 : (2 : ℝ) ^ 62 / (2 : ℝ) ^ 191 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
    have h63 : (2 : ℝ) ^ 63 = 2 * (2 : ℝ) ^ 62 := by
      rw [show (63 : ℕ) = 62 + 1 by decide, pow_succ']
    rw [h191e, h63, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ 62 * (2 : ℝ) ^ 128 by positivity]
  have hεα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
      (cT + ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
          ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape)) /
      ((Goldilocks.order : ℝ) ^ 3) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hterm : ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
        ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤
        17 * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hLJ (by positivity)
    have hnum : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        (cT + ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
            ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape)) ≤ (2 : ℝ) ^ 62 := by
      refine le_trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm) (Nat.cast_nonneg _)) hα_budget
    exact (div_le_div₀ (by positivity) hnum (by positivity) h191).trans h62
  have hεβ : (2 * cT + ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
          ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape)) /
      ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hterm : ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
        ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤
        17 * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hLJ (by positivity)
    have hnum : 2 * cT + ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
        ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤ (2 : ℝ) ^ 62 :=
      (add_le_add le_rfl hterm).trans hβ_budget
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ params.commitPowBits := by
      exact_mod_cast Nat.one_le_pow params.commitPowBits 2 two_pos
    have hnn : 0 ≤ (2 * cT + ((65 / 128 - (1 / 2 : ℝ) ^ params.logBlowup) /
        ((65 / 128 : ℝ) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - 65 / 128) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape)) /
        ((Goldilocks.order : ℝ) ^ 3) := by
      rw [hbl]; positivity
    exact (div_le_self hnn hpow1).trans ((div_le_div₀ (by positivity) hnum (by positivity) h191).trans h62)
  have hεq : (65 / 128 : ℝ) ^ params.numQueries / 2 ^ params.queryPowBits ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [hqpow]
    exact johnson_ge_118_pow20_le_three_quarters_128 hqn
  have hgap : (1 / 2 : ℝ) ^ params.logBlowup < (65 / 128 : ℝ) ^ 2 := by
    rw [hbl]; norm_num
  have hmain := goldilocksExt3_soundness_sponge_blake2b512_johnson params shape hmax hheight s₀ hca
    (θ := 65 / 128) (by norm_num) (by norm_num) hgap hcT0 hT
    (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128) hεα hεβ hεq hadv attempt
  dsimp only at hmain
  have hcol := digest64_sponge_collision_le_quarter_128 (N := N) hN
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at hcol
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rw [← hNcast] at hmain
  refine hmain.trans ?_
  calc (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add le_rfl hcol
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-! ## Unconditional `CurveListCA Fp3Model` Discharge & 128-Bit Johnson Profiles (`lb = 2, 3, 4`) -/

/-- `Fp3Model` has prime characteristic `Goldilocks.order = 2^64 - 2^32 + 1`. -/
theorem charP_fp3Model : CharP Fp3Model Goldilocks.order := by
  constructor
  intro n
  have hcast : (n : Fp3Model) = Fp3Model.embedHom (n : GoldilocksField) := by
    rw [map_natCast]
  rw [hcast, show (0 : Fp3Model) = Fp3Model.embedHom 0 from (map_zero _).symm,
    Fp3Model.embedHom_injective.eq_iff, ZMod.natCast_eq_zero_iff]

/-- **Unconditional `CurveListCA` over Goldilocks cubic extension `Fp3Model`!**
Directly discharges the `CurveListCA` hypothesis with ZERO axioms beyond standard
Lean (`propext`, `Classical.choice`, `Quot.sound`) via
`CurveListCAProof.curveListCA_of_fintype_char`, since `|Fp3Model| = p^3 ≤ p^4`. -/
theorem curveListCA_fp3 :
    CurveListCA Fp3Model CurveListCAProof.curveListThreshold := by
  let _ : CharP Fp3Model Goldilocks.order := charP_fp3Model
  refine CurveListCAProof.curveListCA_of_fintype_char (p := Goldilocks.order)
    (by unfold Goldilocks.order; decide) ?_
  rw [Fp3Model.card_fp3Model]
  exact Nat.pow_le_pow_right (by unfold Goldilocks.order; decide) (by decide)

/-- Tight lower bound `(99 / 100) * 2 ^ 192 ≤ Goldilocks.order ^ 3`. -/
theorem ninetyNine_hundredths_two_pow_192_le_goldilocks_cube :
    (99 / 100 : ℝ) * (2 : ℝ) ^ 192 ≤ (Goldilocks.order : ℝ) ^ 3 := by
  have hord : (2 : ℝ) ^ 64 * (999 / 1000) ≤ (Goldilocks.order : ℝ) := by
    unfold Goldilocks.order
    norm_num
  have hpow : (99 / 100 : ℝ) * (2 : ℝ) ^ 192 ≤ ((2 : ℝ) ^ 64 * (999 / 1000)) ^ 3 := by
    rw [mul_pow, ← pow_mul, show 64 * 3 = 192 by decide]
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ 192 := by positivity
    nlinarith [show (99 / 100 : ℝ) ≤ (999 / 1000 : ℝ) ^ 3 by norm_num]
  exact hpow.trans (pow_le_pow_left₀ (by positivity) hord 3)

/-- Explicit per-degree `curveListCoeff` constant for blowup factor `B` and uniform
Guruswami–Sudan bounds `(Rmax, Lmax)`. -/
def curveListRatioBound (B Rmax Lmax : ℕ) : ℕ :=
  let Zmax := (Rmax + 1) * Lmax
  let B3c := ((Lmax ^ 2 + 4 * Lmax + 4) + 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1)) * Zmax
  let B4c := (4 * Lmax + 2) * Zmax + B * (Zmax + Lmax)
  max (B * (B + 1)) (max ((2 * Lmax + 1) * Rmax * B) (2 * Zmax + Lmax * max B3c B4c))

/-- Uniform linear-in-`d` bound on `CurveListCAProof.curveListCoeff (B * d) d A`
for every `1 ≤ d` when `A = ⌈(p / q) * (B * d)⌉₊` lies above the Johnson threshold
`q ^ 2 < B * p ^ 2`. -/
theorem curveListCoeff_le_of_ratio {n d A B p q Rmax Lmax : ℕ}
    (hd : 1 ≤ d) (hB : 2 ≤ B) (hn : n = B * d) (hq : 0 < q)
    (hgap : q ^ 2 < B * p ^ 2)
    (hA_lo : p * n ≤ q * A) (hA_hi : q * (A - 1) < p * n) (hA_le : A ≤ n) (hA_pos : 1 ≤ A)
    (hR : (2 * q ^ 2) / (B * p ^ 2 - q ^ 2) + 1 ≤ Rmax)
    (hL : (2 * q ^ 2 * p * B + q ^ 3 + 2 * (B * p ^ 2 - q ^ 2) * p * B) /
      ((B * p ^ 2 - q ^ 2) * q) ≤ Lmax) :
    CurveListCAProof.curveListCoeff n d A ≤ curveListRatioBound B Rmax Lmax * d := by
  have hd0 : d ≠ 0 := by omega
  unfold CurveListCAProof.curveListCoeff curveListRatioBound
  rw [ite_eq_right hd0]
  by_cases hd1 : d = 1
  · subst hd1
    simp only [↓reduceIte, mul_one] at hn ⊢
    rw [hn]
    have hdiv : B / A ≤ B := Nat.div_le_self B A
    exact (Nat.mul_le_mul_left B (Nat.add_le_add_right hdiv 1)).trans (le_max_left _ _)
  · rw [ite_eq_right hd1]
    have hd2 : 2 ≤ d := by omega
    have hn_pos : 0 < n := by rw [hn]; positivity
    have hd_pos : 0 < d := by omega
    set Δ := B * p ^ 2 - q ^ 2 with hΔ_def
    have hΔ_pos : 0 < Δ := Nat.sub_pos_of_lt hgap
    -- Lower bound `q^2 * (A^2 - n * (d - 1)) ≥ Δ * d * n`.
    have hden_lb : Δ * d * n ≤ q ^ 2 * (A ^ 2 - n * (d - 1)) := by
      have hsq : p ^ 2 * n ^ 2 ≤ q ^ 2 * A ^ 2 := by
        calc p ^ 2 * n ^ 2 = (p * n) ^ 2 := by ring
          _ ≤ (q * A) ^ 2 := Nat.pow_le_pow_left hA_lo 2
          _ = q ^ 2 * A ^ 2 := by ring
      have hpn2 : p ^ 2 * n ^ 2 = B * p ^ 2 * d * n := by
        rw [hn]; ring
      have hnd1 : q ^ 2 * (n * (d - 1)) ≤ q ^ 2 * d * n := by
        calc q ^ 2 * (n * (d - 1)) = q ^ 2 * (d - 1) * n := by ring
          _ ≤ q ^ 2 * d * n :=
            Nat.mul_le_mul_right n (Nat.mul_le_mul_left (q ^ 2) (Nat.sub_le d 1))
      have hadd : Δ * d * n + q ^ 2 * (n * (d - 1)) ≤ q ^ 2 * A ^ 2 := by
        have hsum : Δ * d * n + q ^ 2 * d * n = B * p ^ 2 * d * n := by
          have h1 : Δ + q ^ 2 = B * p ^ 2 := Nat.sub_add_cancel (le_of_lt hgap)
          calc Δ * d * n + q ^ 2 * d * n = (Δ + q ^ 2) * d * n := by ring
            _ = B * p ^ 2 * d * n := by rw [h1]
        calc Δ * d * n + q ^ 2 * (n * (d - 1))
            ≤ Δ * d * n + q ^ 2 * d * n := Nat.add_le_add_left hnd1 _
          _ = B * p ^ 2 * d * n := hsum
          _ = p ^ 2 * n ^ 2 := hpn2.symm
          _ ≤ q ^ 2 * A ^ 2 := hsq
      rw [Nat.mul_sub_left_distrib]
      exact Nat.le_sub_of_add_le hadd
    -- Bound `r0 = (2 * (d - 1) * n) / (A ^ 2 - n * (d - 1))` and `r = r0 + 1`.
    set r0 := (2 * (d - 1) * n) / (A ^ 2 - n * (d - 1))
    have hr0_mul : r0 * Δ * d ≤ 2 * q ^ 2 * (d - 1) := by
      have h1 : r0 * (A ^ 2 - n * (d - 1)) ≤ 2 * (d - 1) * n := Nat.div_mul_le_self _ _
      have h2 : (r0 * Δ * d) * n ≤ (2 * q ^ 2 * (d - 1)) * n := by
        calc (r0 * Δ * d) * n = r0 * (Δ * d * n) := by ring
          _ ≤ r0 * (q ^ 2 * (A ^ 2 - n * (d - 1))) := Nat.mul_le_mul_left r0 hden_lb
          _ = q ^ 2 * (r0 * (A ^ 2 - n * (d - 1))) := by ring
          _ ≤ q ^ 2 * (2 * (d - 1) * n) := Nat.mul_le_mul_left (q ^ 2) h1
          _ = (2 * q ^ 2 * (d - 1)) * n := by ring
      exact Nat.le_of_mul_le_mul_right h2 hn_pos
    have hr_le : CurveListCAProof.gsMult n d A ≤ Rmax := by
      have hr0_le : r0 * Δ ≤ 2 * q ^ 2 := by
        have h1 : (r0 * Δ) * d ≤ (2 * q ^ 2) * d :=
          hr0_mul.trans (Nat.mul_le_mul_left (2 * q ^ 2) (Nat.sub_le d 1))
        exact Nat.le_of_mul_le_mul_right h1 hd_pos
      have hr0_div : r0 ≤ (2 * q ^ 2) / Δ := (Nat.le_div_iff_mul_le hΔ_pos).mpr hr0_le
      show r0 + 1 ≤ Rmax
      omega
    -- Bound `L_Y = gsDegY n d A ≤ Lmax` uniformly across all `d ≥ 2`.
    have hL_le : CurveListCAProof.gsDegY n d A ≤ Lmax := by
      have hqA_le : q * A ≤ p * B * d + q := by
        have h1 : q * A = q * (A - 1) + q := by
          calc q * A = q * ((A - 1) + 1) := by rw [Nat.sub_add_cancel hA_pos]
            _ = q * (A - 1) + q := by ring
        rw [h1, hn] at *
        have h2 : q * (A - 1) ≤ p * (B * d) := le_of_lt hA_hi
        calc q * (A - 1) + q ≤ p * (B * d) + q := Nat.add_le_add_right h2 q
          _ = p * B * d + q := by ring
      have hpart1 : r0 * Δ * q * A ≤ (2 * q ^ 2 * p * B + q ^ 3) * (d - 1) := by
        have h1 : (r0 * Δ * q * A) * d ≤ (2 * q ^ 2 * p * B + q ^ 3) * (d - 1) * d := by
          have h2q : 2 * q ^ 2 * (d - 1) * q ≤ q ^ 3 * (d - 1) * d := by
            have h2d : 2 ≤ d := hd2
            calc 2 * q ^ 2 * (d - 1) * q = (q ^ 3 * (d - 1)) * 2 := by ring
              _ ≤ (q ^ 3 * (d - 1)) * d := Nat.mul_le_mul_left _ h2d
          calc (r0 * Δ * q * A) * d = (r0 * Δ * d) * (q * A) := by ring
            _ ≤ (2 * q ^ 2 * (d - 1)) * (p * B * d + q) := Nat.mul_le_mul hr0_mul hqA_le
            _ = 2 * q ^ 2 * p * B * (d - 1) * d + 2 * q ^ 2 * (d - 1) * q := by ring
            _ ≤ 2 * q ^ 2 * p * B * (d - 1) * d + q ^ 3 * (d - 1) * d :=
                Nat.add_le_add_left h2q _
            _ = (2 * q ^ 2 * p * B + q ^ 3) * (d - 1) * d := by ring
        exact Nat.le_of_mul_le_mul_right h1 hd_pos
      have hpart2 : Δ * q * (A - 1) ≤ 2 * Δ * p * B * (d - 1) := by
        have hd2m : d ≤ 2 * (d - 1) := by omega
        have h1 : q * (A - 1) ≤ p * B * d := by
          rw [hn] at hA_hi
          calc q * (A - 1) ≤ p * (B * d) := le_of_lt hA_hi
            _ = p * B * d := by ring
        calc Δ * q * (A - 1) = Δ * (q * (A - 1)) := by ring
          _ ≤ Δ * (p * B * d) := Nat.mul_le_mul_left Δ h1
          _ = (Δ * p * B) * d := by ring
          _ ≤ (Δ * p * B) * (2 * (d - 1)) := Nat.mul_le_mul_left _ hd2m
          _ = 2 * Δ * p * B * (d - 1) := by ring
      have hDX_eq : CurveListCAProof.gsDegX n d A = r0 * A + (A - 1) := by
        unfold CurveListCAProof.gsDegX CurveListCAProof.gsMult
        show (r0 + 1) * A - 1 = r0 * A + (A - 1)
        rw [Nat.add_mul, one_mul, Nat.add_sub_assoc hA_pos]
      have hDX_mul : (Δ * q) * CurveListCAProof.gsDegX n d A ≤
          (2 * q ^ 2 * p * B + q ^ 3 + 2 * Δ * p * B) * (d - 1) := by
        rw [hDX_eq]
        calc (Δ * q) * (r0 * A + (A - 1)) = r0 * Δ * q * A + Δ * q * (A - 1) := by ring
          _ ≤ (2 * q ^ 2 * p * B + q ^ 3) * (d - 1) + 2 * Δ * p * B * (d - 1) :=
              Nat.add_le_add hpart1 hpart2
          _ = (2 * q ^ 2 * p * B + q ^ 3 + 2 * Δ * p * B) * (d - 1) := by ring
      have hLY_eq : CurveListCAProof.gsDegY n d A = CurveListCAProof.gsDegX n d A / (d - 1) := by
        unfold CurveListCAProof.gsDegY
        rw [ite_eq_right (by omega)]
      have hLY_mul : CurveListCAProof.gsDegY n d A * (Δ * q) ≤
          2 * q ^ 2 * p * B + q ^ 3 + 2 * Δ * p * B := by
        have h1 : (CurveListCAProof.gsDegY n d A * (Δ * q)) * (d - 1) ≤
            (2 * q ^ 2 * p * B + q ^ 3 + 2 * Δ * p * B) * (d - 1) := by
          have hdiv : CurveListCAProof.gsDegY n d A * (d - 1) ≤ CurveListCAProof.gsDegX n d A := by
            rw [hLY_eq]; exact Nat.div_mul_le_self _ _
          calc (CurveListCAProof.gsDegY n d A * (Δ * q)) * (d - 1)
              = (Δ * q) * (CurveListCAProof.gsDegY n d A * (d - 1)) := by ring
            _ ≤ (Δ * q) * CurveListCAProof.gsDegX n d A := Nat.mul_le_mul_left _ hdiv
            _ ≤ (2 * q ^ 2 * p * B + q ^ 3 + 2 * Δ * p * B) * (d - 1) := hDX_mul
        exact Nat.le_of_mul_le_mul_right h1 (by omega)
      exact ((Nat.le_div_iff_mul_le (Nat.mul_pos hΔ_pos hq)).mpr hLY_mul).trans hL
    -- Assemble the polynomial-in-`(Rmax, Lmax)` bound multiplied by `d`.
    set r := CurveListCAProof.gsMult n d A
    set D_X := CurveListCAProof.gsDegX n d A
    set L_Y := CurveListCAProof.gsDegY n d A
    set D_Z1 := (r + 1) * L_Y
    set Zmax := (Rmax + 1) * Lmax
    have hDZ1_le : D_Z1 ≤ Zmax :=
      Nat.mul_le_mul (Nat.add_le_add_right hr_le 1) hL_le
    have hDX_le : D_X ≤ Rmax * B * d := by
      have h1 : D_X ≤ r * A := Nat.sub_le _ 1
      calc D_X ≤ r * A := h1
        _ ≤ Rmax * n := Nat.mul_le_mul hr_le hA_le
        _ = Rmax * B * d := by rw [hn]; ring
    have hterm1 : (2 * L_Y + 1) * D_X ≤ ((2 * Lmax + 1) * Rmax * B) * d := by
      calc (2 * L_Y + 1) * D_X ≤ (2 * Lmax + 1) * (Rmax * B * d) :=
            Nat.mul_le_mul (by omega) hDX_le
        _ = ((2 * Lmax + 1) * Rmax * B) * d := by ring
    have hB3_le : ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z1 ≤
        (((Lmax ^ 2 + 4 * Lmax + 4) + 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1)) * Zmax) * d := by
      have hq1 : L_Y ^ 2 + 4 * L_Y + 4 ≤ (Lmax ^ 2 + 4 * Lmax + 4) * d := by
        have hsq : L_Y ^ 2 ≤ Lmax ^ 2 := Nat.pow_le_pow_left hL_le 2
        have hle : L_Y ^ 2 + 4 * L_Y + 4 ≤ Lmax ^ 2 + 4 * Lmax + 4 := by omega
        exact hle.trans (Nat.le_mul_of_pos_right _ hd_pos)
      have hq2 : 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1) ≤
          2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1) * d := by
        have hsq : L_Y ^ 2 ≤ Lmax ^ 2 := Nat.pow_le_pow_left hL_le 2
        have hm1 : 2 * L_Y * (L_Y ^ 2 + 4 * L_Y + 1) ≤ 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        calc 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)
            = (2 * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * d := by ring
          _ ≤ (2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1)) * d := Nat.mul_le_mul_right d hm1
      calc ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z1
          ≤ ((Lmax ^ 2 + 4 * Lmax + 4) * d + 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1) * d) * Zmax :=
            Nat.mul_le_mul (Nat.add_le_add hq1 hq2) hDZ1_le
        _ = (((Lmax ^ 2 + 4 * Lmax + 4) + 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1)) * Zmax) * d := by ring
    have hB4_le : (4 * L_Y + 2) * D_Z1 + n * (D_Z1 + L_Y) ≤
        ((4 * Lmax + 2) * Zmax + B * (Zmax + Lmax)) * d := by
      have h1 : (4 * L_Y + 2) * D_Z1 ≤ ((4 * Lmax + 2) * Zmax) * d :=
        (Nat.mul_le_mul (by omega) hDZ1_le).trans (Nat.le_mul_of_pos_right _ hd_pos)
      have h2 : n * (D_Z1 + L_Y) ≤ (B * (Zmax + Lmax)) * d := by
        rw [hn]
        calc B * d * (D_Z1 + L_Y) = (B * (D_Z1 + L_Y)) * d := by ring
          _ ≤ (B * (Zmax + Lmax)) * d :=
            Nat.mul_le_mul_right d (Nat.mul_le_mul_left B (Nat.add_le_add hDZ1_le hL_le))
      calc (4 * L_Y + 2) * D_Z1 + n * (D_Z1 + L_Y)
          ≤ ((4 * Lmax + 2) * Zmax) * d + (B * (Zmax + Lmax)) * d := Nat.add_le_add h1 h2
        _ = ((4 * Lmax + 2) * Zmax + B * (Zmax + Lmax)) * d := by ring
    have hterm2 : 2 * D_Z1 + L_Y * max
        (((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z1)
        ((4 * L_Y + 2) * D_Z1 + n * (D_Z1 + L_Y)) ≤
        (2 * Zmax + Lmax * max
          (((Lmax ^ 2 + 4 * Lmax + 4) + 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1)) * Zmax)
          ((4 * Lmax + 2) * Zmax + B * (Zmax + Lmax))) * d := by
      have h2Z : 2 * D_Z1 ≤ (2 * Zmax) * d :=
        (Nat.mul_le_mul_left 2 hDZ1_le).trans (Nat.le_mul_of_pos_right _ hd_pos)
      have hmax_le : max
          (((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z1)
          ((4 * L_Y + 2) * D_Z1 + n * (D_Z1 + L_Y)) ≤
          max (((Lmax ^ 2 + 4 * Lmax + 4) + 2 * Lmax * (Lmax ^ 2 + 4 * Lmax + 1)) * Zmax)
            ((4 * Lmax + 2) * Zmax + B * (Zmax + Lmax)) * d := by
        rw [max_le_iff]
        exact ⟨hB3_le.trans (Nat.mul_le_mul_right d (le_max_left _ _)),
          hB4_le.trans (Nat.mul_le_mul_right d (le_max_right _ _))⟩
      calc 2 * D_Z1 + L_Y * max _ _
          ≤ (2 * Zmax) * d + Lmax * (max _ _ * d) :=
            Nat.add_le_add h2Z (Nat.mul_le_mul hL_le hmax_le)
        _ = (2 * Zmax + Lmax * max _ _) * d := by ring
    refine max_le ?_ ?_
    · exact hterm1.trans (Nat.mul_le_mul_right d
        ((le_max_left _ _).trans (le_max_right _ _)))
    · exact hterm2.trans (Nat.mul_le_mul_right d
        ((le_max_right _ _).trans (le_max_right _ _)))

/-! ### Query-Soundness Arithmetic Lemmas for All 4 Johnson Profiles -/

private theorem pow_div_pow2_le_three_quarters_128 {a n e : ℕ}
    (ha : (a : ℕ) ^ n * 4 ≤ 3 * 2 ^ e) :
    (a : ℝ) ^ n / ((2 : ℝ) ^ e * (2 : ℝ) ^ 128) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have har : (a : ℝ) ^ n * 4 ≤ 3 * (2 : ℝ) ^ e := by exact_mod_cast ha
  have hpose : (0 : ℝ) < (2 : ℝ) ^ e := pow_pos (by norm_num) e
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  rw [div_le_div_iff₀ (mul_pos hpose hpos128) hpos128]
  have hmul : (a : ℝ) ^ n * 4 * (2 : ℝ) ^ 128 ≤ (3 * (2 : ℝ) ^ e) * (2 : ℝ) ^ 128 :=
    mul_le_mul_of_nonneg_right har hpos128.le
  have h1 : (4 : ℝ) * ((a : ℝ) ^ n * (2 : ℝ) ^ 128) ≤
      (4 : ℝ) * ((3 / 4 : ℝ) * ((2 : ℝ) ^ e * (2 : ℝ) ^ 128)) := by
    calc (4 : ℝ) * ((a : ℝ) ^ n * (2 : ℝ) ^ 128)
        = (a : ℝ) ^ n * 4 * (2 : ℝ) ^ 128 := by rw [← mul_assoc, mul_comm (4 : ℝ)]
      _ ≤ (3 * (2 : ℝ) ^ e) * (2 : ℝ) ^ 128 := hmul
      _ = (4 : ℝ) * ((3 / 4 : ℝ) * ((2 : ℝ) ^ e * (2 : ℝ) ^ 128)) := by
          rw [mul_assoc, ← mul_assoc (4 : ℝ) (3 / 4 : ℝ), show (4 : ℝ) * (3 / 4 : ℝ) = 3 by norm_num]
  exact le_of_mul_le_mul_left h1 (by norm_num)

/-- `(lb = 2, q ≥ 128, queryPow = 20)` at `θ = 71 / 128` (`128.83` query bits). -/
theorem johnson_71_128_ge_128_pow20_le_three_quarters_128 {q : ℕ} (hq : 128 ≤ q) :
    ((71 / 128 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono : (71 / 128 : ℝ) ^ q ≤ (71 / 128 : ℝ) ^ 128 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have h71 : (71 : ℕ) ^ 128 * 4 ≤ 3 * 2 ^ 788 := by
    have h32 : (71 : ℕ) ^ 32 * 100 ≤ 87 * 2 ^ 197 := by norm_num
    have hpow := Nat.pow_le_pow_left h32 4
    have h87 : (87 : ℕ) ^ 4 * 4 ≤ 3 * 100 ^ 4 := by norm_num
    have hmul : (71 : ℕ) ^ 128 * 100 ^ 4 * 4 ≤ 3 * 100 ^ 4 * 2 ^ 788 := by
      calc (71 : ℕ) ^ 128 * 100 ^ 4 * 4
          = ((71 ^ 32 * 100) ^ 4) * 4 := by rw [mul_pow, ← pow_mul]
        _ ≤ ((87 * 2 ^ 197) ^ 4) * 4 := Nat.mul_le_mul_right 4 hpow
        _ = (87 ^ 4 * 4) * 2 ^ 788 := by rw [mul_pow, ← pow_mul, mul_right_comm]
        _ ≤ (3 * 100 ^ 4) * 2 ^ 788 := Nat.mul_le_mul_right _ h87
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (100 : ℕ) ^ 4 by decide)
    calc (100 : ℕ) ^ 4 * (71 ^ 128 * 4) = 71 ^ 128 * 100 ^ 4 * 4 := by
          rw [← mul_assoc, mul_comm (100 ^ 4) (71 ^ 128)]
      _ ≤ 3 * 100 ^ 4 * 2 ^ 788 := hmul
      _ = 100 ^ 4 * (3 * 2 ^ 788) := by rw [mul_comm 3 (100 ^ 4), mul_assoc]
  have h128 : ((71 / 128 : ℝ) ^ 128) / (2 : ℝ) ^ 20 = (71 : ℝ) ^ 128 / (2 : ℝ) ^ 916 := by
    rw [div_pow, div_div, show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num, ← pow_mul, ← pow_add]
  have h916 : (2 : ℝ) ^ 916 = (2 : ℝ) ^ 788 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  have hbase : ((71 / 128 : ℝ) ^ 128) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [h128, h916]
    exact pow_div_pow2_le_three_quarters_128 h71
  exact (div_le_div_of_nonneg_right hmono (by positivity)).trans hbase

/-- `(lb = 2, q ≥ 118, queryPow = 20)` at `θ = 135 / 256` (`128.94` query bits). -/
theorem johnson_135_256_ge_118_pow20_le_three_quarters_128 {q : ℕ} (hq : 118 ≤ q) :
    ((135 / 256 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono : (135 / 256 : ℝ) ^ q ≤ (135 / 256 : ℝ) ^ 118 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have h135 : (135 : ℕ) ^ 118 * 4 ≤ 3 * 2 ^ 836 := by
    have h30 : (135 : ℕ) ^ 30 * 100 ≤ 124 * 2 ^ 212 := by norm_num
    have h29 : (135 : ℕ) ^ 29 * 100 ≤ 59 * 2 ^ 206 := by norm_num
    have h59 : (135 : ℕ) ^ 59 * 10000 ≤ 7316 * 2 ^ 418 := by
      have hm := Nat.mul_le_mul h30 h29
      calc (135 : ℕ) ^ 59 * 10000 = (135 ^ 30 * 100) * (135 ^ 29 * 100) := by
            rw [show 59 = 30 + 29 by decide, pow_add, show (10000 : ℕ) = 100 * 100 by decide,
              mul_mul_mul_comm]
        _ ≤ (124 * 2 ^ 212) * (59 * 2 ^ 206) := hm
        _ = 7316 * 2 ^ 418 := by
            rw [mul_mul_mul_comm, ← pow_add, show 124 * 59 = 7316 by decide,
              show 212 + 206 = 418 by decide]
    have hpow := Nat.pow_le_pow_left h59 2
    have h73 : (7316 : ℕ) ^ 2 * 4 ≤ 3 * 10000 ^ 2 := by norm_num
    have hmul : (135 : ℕ) ^ 118 * 10000 ^ 2 * 4 ≤ 3 * 10000 ^ 2 * 2 ^ 836 := by
      calc (135 : ℕ) ^ 118 * 10000 ^ 2 * 4
          = ((135 ^ 59 * 10000) ^ 2) * 4 := by rw [mul_pow, ← pow_mul]
        _ ≤ ((7316 * 2 ^ 418) ^ 2) * 4 := Nat.mul_le_mul_right 4 hpow
        _ = (7316 ^ 2 * 4) * 2 ^ 836 := by rw [mul_pow, ← pow_mul, mul_right_comm]
        _ ≤ (3 * 10000 ^ 2) * 2 ^ 836 := Nat.mul_le_mul_right _ h73
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (10000 : ℕ) ^ 2 by decide)
    calc (10000 : ℕ) ^ 2 * (135 ^ 118 * 4) = 135 ^ 118 * 10000 ^ 2 * 4 := by
          rw [← mul_assoc, mul_comm (10000 ^ 2) (135 ^ 118)]
      _ ≤ 3 * 10000 ^ 2 * 2 ^ 836 := hmul
      _ = 10000 ^ 2 * (3 * 2 ^ 836) := by rw [mul_comm 3 (10000 ^ 2), mul_assoc]
  have h256 : ((135 / 256 : ℝ) ^ 118) / (2 : ℝ) ^ 20 = (135 : ℝ) ^ 118 / (2 : ℝ) ^ 964 := by
    rw [div_pow, div_div, show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num, ← pow_mul, ← pow_add]
  have h964 : (2 : ℝ) ^ 964 = (2 : ℝ) ^ 836 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  have hbase : ((135 / 256 : ℝ) ^ 118) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [h256, h964]
    exact pow_div_pow2_le_three_quarters_128 h135
  exact (div_le_div_of_nonneg_right hmono (by positivity)).trans hbase

/-- Native STARK Shrinker `(lb = 3, q ≥ 78, queryPow = 20)` at `θ = 19 / 50` (`128.88` query bits). -/
theorem johnson_19_50_ge_78_pow20_le_three_quarters_128 {q : ℕ} (hq : 78 ≤ q) :
    ((19 / 50 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono : (19 / 50 : ℝ) ^ q ≤ (19 / 50 : ℝ) ^ 78 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have h19 : (19 : ℕ) ^ 78 * 2 ^ 32 ≤ 3 * 25 ^ 78 := by
    have h39 : (19 : ℕ) ^ 39 * 2 ^ 16 * 10 ≤ 15 * 25 ^ 39 := by norm_num
    have hpow := Nat.pow_le_pow_left h39 2
    have h15 : (15 : ℕ) ^ 2 ≤ 3 * 10 ^ 2 := by decide
    have hmul : (19 : ℕ) ^ 78 * 2 ^ 32 * 10 ^ 2 ≤ 3 * 10 ^ 2 * 25 ^ 78 := by
      calc (19 : ℕ) ^ 78 * 2 ^ 32 * 10 ^ 2
          = ((19 ^ 39 * 2 ^ 16 * 10) ^ 2) := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        _ ≤ (15 * 25 ^ 39) ^ 2 := hpow
        _ = 15 ^ 2 * 25 ^ 78 := by rw [mul_pow, ← pow_mul]
        _ ≤ (3 * 10 ^ 2) * 25 ^ 78 := Nat.mul_le_mul_right _ h15
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (10 : ℕ) ^ 2 by decide)
    calc (10 : ℕ) ^ 2 * (19 ^ 78 * 2 ^ 32) = 19 ^ 78 * 2 ^ 32 * 10 ^ 2 := by
          rw [mul_comm (10 ^ 2) _]
      _ ≤ 3 * 10 ^ 2 * 25 ^ 78 := hmul
      _ = 10 ^ 2 * (3 * 25 ^ 78) := by rw [mul_comm 3 (10 ^ 2), mul_assoc]
  have h19r : (19 : ℝ) ^ 78 * (2 : ℝ) ^ 32 ≤ 3 * (25 : ℝ) ^ 78 := by exact_mod_cast h19
  have h50 : (50 : ℝ) ^ 78 = (2 : ℝ) ^ 78 * (25 : ℝ) ^ 78 := by
    rw [show (50 : ℝ) = 2 * 25 by norm_num, mul_pow]
  have hbase : ((19 / 50 : ℝ) ^ 78) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity), h50]
    have h128 : (2 : ℝ) ^ 128 = (2 : ℝ) ^ 32 * (2 : ℝ) ^ 96 := by rw [← pow_add]
    have h98 : (2 : ℝ) ^ 78 * (2 : ℝ) ^ 20 = 4 * (2 : ℝ) ^ 96 := by
      rw [← pow_add, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
    have hpos96 : (0 : ℝ) < (2 : ℝ) ^ 96 := by positivity
    calc (19 : ℝ) ^ 78 * (2 : ℝ) ^ 128
        = ((19 : ℝ) ^ 78 * (2 : ℝ) ^ 32) * (2 : ℝ) ^ 96 := by rw [h128, mul_assoc]
      _ ≤ (3 * (25 : ℝ) ^ 78) * (2 : ℝ) ^ 96 := mul_le_mul_of_nonneg_right h19r hpos96.le
      _ = (3 / 4 : ℝ) * ((25 : ℝ) ^ 78 * (4 * (2 : ℝ) ^ 96)) := by ring
      _ = (3 / 4 : ℝ) * ((2 : ℝ) ^ 78 * (25 : ℝ) ^ 78 * (2 : ℝ) ^ 20) := by
          rw [← h98]; ring
  exact (div_le_div_of_nonneg_right hmono (by positivity)).trans hbase

/-- Native STARK Shrinker `(lb = 4, q ≥ 58, queryPow = 20)` at `θ = 35 / 128` (`128.50` query bits). -/
theorem johnson_35_128_ge_58_pow20_le_three_quarters_128 {q : ℕ} (hq : 58 ≤ q) :
    ((35 / 128 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono : (35 / 128 : ℝ) ^ q ≤ (35 / 128 : ℝ) ^ 58 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have h35 : (35 : ℕ) ^ 58 * 4 ≤ 3 * 2 ^ 298 := by
    have h29 : (35 : ℕ) ^ 29 * 100 ≤ 85 * 2 ^ 149 := by norm_num
    have hpow := Nat.pow_le_pow_left h29 2
    have h85 : (85 : ℕ) ^ 2 * 4 ≤ 3 * 100 ^ 2 := by decide
    have hmul : (35 : ℕ) ^ 58 * 100 ^ 2 * 4 ≤ 3 * 100 ^ 2 * 2 ^ 298 := by
      calc (35 : ℕ) ^ 58 * 100 ^ 2 * 4
          = ((35 ^ 29 * 100) ^ 2) * 4 := by rw [mul_pow, ← pow_mul]
        _ ≤ ((85 * 2 ^ 149) ^ 2) * 4 := Nat.mul_le_mul_right 4 hpow
        _ = (85 ^ 2 * 4) * 2 ^ 298 := by rw [mul_pow, ← pow_mul, mul_right_comm]
        _ ≤ (3 * 100 ^ 2) * 2 ^ 298 := Nat.mul_le_mul_right _ h85
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (100 : ℕ) ^ 2 by decide)
    calc (100 : ℕ) ^ 2 * (35 ^ 58 * 4) = 35 ^ 58 * 100 ^ 2 * 4 := by
          rw [← mul_assoc, mul_comm (100 ^ 2) (35 ^ 58)]
      _ ≤ 3 * 100 ^ 2 * 2 ^ 298 := hmul
      _ = 100 ^ 2 * (3 * 2 ^ 298) := by rw [mul_comm 3 (100 ^ 2), mul_assoc]
  have h128 : ((35 / 128 : ℝ) ^ 58) / (2 : ℝ) ^ 20 = (35 : ℝ) ^ 58 / (2 : ℝ) ^ 426 := by
    rw [div_pow, div_div, show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num, ← pow_mul, ← pow_add]
  have h426 : (2 : ℝ) ^ 426 = (2 : ℝ) ^ 298 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  have hbase : ((35 / 128 : ℝ) ^ 58) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [h128, h426]
    exact pow_div_pow2_le_three_quarters_128 h35
  exact (div_le_div_of_nonneg_right hmono (by positivity)).trans hbase

/-! ### Master Unconditional Profile Instantiation (Zero `CurveListCA` Hypothesis!) -/

/-- **Master Unconditional 128-Bit Johnson Soundness Schema over `GoldilocksExt3` (`Digest64`,
RFC 7693 `BLAKE2b-512`):** discharges `CurveListCA Fp3Model CurveListCAProof.curveListThreshold`
internally via `curveListCA_fp3` and bounds `curveListCoeff` across all folding rounds uniformly
via `curveListCoeff_le_of_ratio`, producing literal `≤ N / 2 ^ 128` executable `Fri.verify`
soundness for any verified rational Johnson profile `(lb, p / q, Rmax, Lmax, PowExp, Hmax, ClaimExp)`. -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson_of_profile
    (lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp : ℕ)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = lb) (hlb : 1 ≤ lb)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ Hmax) (hmax32 : Hmax ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ ClaimExp)
    (hq : ((p : ℝ) / q) ^ params.numQueries / 2 ^ params.queryPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128)
    (hq_pos : 0 < q) (hpq : p ≤ q) (hgap_nat : q ^ 2 < 2 ^ lb * p ^ 2)
    (hR : (2 * q ^ 2) / (2 ^ lb * p ^ 2 - q ^ 2) + 1 ≤ Rmax)
    (hL : (2 * q ^ 2 * p * 2 ^ lb + q ^ 3 + 2 * (2 ^ lb * p ^ 2 - q ^ 2) * p * 2 ^ lb) /
      ((2 ^ lb * p ^ 2 - q ^ 2) * q) ≤ Lmax)
    (hLJ : (((p : ℝ) / q - (1 / 2 : ℝ) ^ lb) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ lb)) * (1 - (p : ℝ) / q) ≤ LJ_ub)
    (hCd : curveListRatioBound (2 ^ lb) Rmax Lmax + 2 ^ lb * LJ_ub ≤ 2 ^ lb * 2 ^ PowExp)
    (hClaimExp : ClaimExp + PowExp ≤ 63)
    (hHmax : Hmax + PowExp + 1 ≤ 63)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hmax32)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift ((p : ℝ) / q)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  intro wf P N
  set H := Fri.logMaxHeight params.logBlowup shape
  set B : ℕ := 2 ^ lb
  have hB2 : 2 ≤ B := by
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ lb := Nat.pow_le_pow_right two_pos hlb
  have hp_pos : 0 < p := by
    by_contra hp0
    have hpz : p = 0 := by omega
    subst hpz
    have hq2_pos : 0 < q ^ 2 := pow_pos hq_pos 2
    simp at hgap_nat
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := div_pos (Nat.cast_pos.mpr hp_pos) (Nat.cast_pos.mpr hq_pos)
  have hθ1 : (p : ℝ) / q ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hq_pos)]
    exact_mod_cast hpq
  have hgap : (1 / 2 : ℝ) ^ params.logBlowup < ((p : ℝ) / q) ^ 2 := by
    rw [hbl, div_pow, one_pow, div_pow]
    have hgap_r : ((q : ℝ) ^ 2) < (2 : ℝ) ^ lb * (p : ℝ) ^ 2 := by exact_mod_cast hgap_nat
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm ((p : ℝ) ^ 2)]
    exact hgap_r
  set Cd := curveListRatioBound B Rmax Lmax
  set cT : ℝ := ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H
  have hcT0 : 0 ≤ cT := by positivity
  -- Verify `hT` across every round `j ≤ numRounds` and every `k ≥ 2`.
  have hT : ∀ (j k : ℕ), j ≤ Fri.numRounds params shape → 2 ≤ k →
      (CurveListCAProof.curveListThreshold (2 ^ (H - j))
        (2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - j)⌉₊ k : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * cT := by
    intro j k hj hk
    set nj : ℕ := 2 ^ (H - j)
    set dj : ℕ := 2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen
    set Aj : ℕ := ⌈((p : ℝ) / q) * (nj : ℝ)⌉₊
    have hH_eq : H = Fri.numRounds params shape + lb + params.logFinalPolyLen := by
      have h1 : Fri.numRounds params shape = H - params.logFinalHeight := rfl
      have h2 : params.logFinalHeight ≤ H := hheight
      unfold FriParams.logFinalHeight at h1 h2
      rw [hbl] at h1 h2
      omega
    have hnj_eq : nj = B * dj := by
      dsimp only [nj, dj, B]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hdj_pos : 1 ≤ dj := Nat.mul_pos (pow_pos two_pos _) (pow_pos two_pos _)
    have hnj_pos : 0 < nj := pow_pos two_pos _
    have hprod_pos : (0 : ℝ) < ((p : ℝ) / q) * (nj : ℝ) :=
      mul_pos hθ0 (Nat.cast_pos.mpr hnj_pos)
    have hAj_pos : 1 ≤ Aj := Nat.ceil_pos.mpr hprod_pos
    have hAj_le : Aj ≤ nj := by
      apply Nat.ceil_le.mpr
      calc ((p : ℝ) / q) * (nj : ℝ) ≤ 1 * (nj : ℝ) :=
            mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg _)
        _ = (nj : ℝ) := one_mul _
    have hAj_lo : p * nj ≤ q * Aj := by
      have h1 : ((p : ℝ) / q) * (nj : ℝ) ≤ (Aj : ℝ) := Nat.le_ceil _
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (p : ℝ) * (nj : ℝ) ≤ (q : ℝ) * (Aj : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hq_r.le
        field_simp [hq_r.ne'] at this
        linarith
      exact_mod_cast h2
    have hAj_hi : q * (Aj - 1) < p * nj := by
      have h1 : (Aj : ℝ) < ((p : ℝ) / q) * (nj : ℝ) + 1 := Nat.ceil_lt_add_one hprod_pos.le
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (q : ℝ) * ((Aj - 1 : ℕ) : ℝ) < (p : ℝ) * (nj : ℝ) := by
        rw [Nat.cast_sub hAj_pos, Nat.cast_one]
        have hsub : (Aj : ℝ) - 1 < ((p : ℝ) / q) * (nj : ℝ) := by linarith
        have := mul_lt_mul_of_pos_left hsub hq_r
        field_simp [hq_r.ne'] at this
        linarith
      exact_mod_cast h2
    have hnat1 : CurveListCAProof.curveListThreshold nj dj Aj k ≤
        (k - 1) * CurveListCAProof.curveListCoeff nj dj Aj :=
      CurveListCAProof.curveListThreshold_le_mul_coeff nj dj Aj k hk
    have hnat2 : CurveListCAProof.curveListCoeff nj dj Aj ≤ Cd * dj :=
      curveListCoeff_le_of_ratio hdj_pos hB2 hnj_eq hq_pos hgap_nat hAj_lo hAj_hi hAj_le hAj_pos hR hL
    have hnat : CurveListCAProof.curveListThreshold nj dj Aj k ≤ (k - 1) * (Cd * dj) :=
      hnat1.trans (Nat.mul_le_mul_left (k - 1) hnat2)
    have hdj_le : (dj : ℝ) ≤ (2 : ℝ) ^ H / (B : ℝ) := by
      have hBdj : B * dj ≤ 2 ^ H := by
        rw [← hnj_eq]
        exact Nat.pow_le_pow_right two_pos (Nat.sub_le H j)
      have hBdj_r : (B : ℝ) * (dj : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast hBdj
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hcast : ((CurveListCAProof.curveListThreshold nj dj Aj k : ℕ) : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * ((Cd : ℝ) * (dj : ℝ)) := by
      exact_mod_cast hnat
    have hnj_cast : ((nj : ℕ) : ℝ) = (2 : ℝ) ^ (H - j) := by
      dsimp only [nj]; push_cast; rfl
    rw [← hnj_cast]
    refine hcast.trans ?_
    dsimp only [cT]
    have hstep : (Cd : ℝ) * (dj : ℝ) ≤ ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H := by
      calc (Cd : ℝ) * (dj : ℝ) ≤ (Cd : ℝ) * ((2 : ℝ) ^ H / (B : ℝ)) :=
            mul_le_mul_of_nonneg_left hdj_le (Nat.cast_nonneg _)
        _ = ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H := by ring
    exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
  -- Prove `2^63 / p^3 ≤ (3/4) / 2^128` via `(99/100) * 2^192 ≤ p^3`.
  have h63 : (2 : ℝ) ^ 63 / ((Goldilocks.order : ℝ) ^ 3) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    refine (div_le_div_of_nonneg_left (by positivity) (by positivity)
      ninetyNine_hundredths_two_pow_192_le_goldilocks_cube).trans ?_
    rw [show (2 : ℝ) ^ 192 = (2 : ℝ) ^ 64 * (2 : ℝ) ^ 128 by rw [← pow_add],
      show (2 : ℝ) ^ 64 = 2 * (2 : ℝ) ^ 63 by rw [show (64 : ℕ) = 63 + 1 by decide, pow_succ'],
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 by positivity]
  -- Combined per-height factor `cT + LJ * (1 - θ) * 2^H ≤ 2^PowExp * 2^H`.
  have hcomb : cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (2 : ℝ) ^ PowExp * (2 : ℝ) ^ H := by
    have hCd_r : (Cd : ℝ) + (B : ℝ) * (LJ_ub : ℝ) ≤ (B : ℝ) * (2 : ℝ) ^ PowExp := by
      exact_mod_cast hCd
    have hfrac : (Cd : ℝ) / (B : ℝ) + (LJ_ub : ℝ) ≤ (2 : ℝ) ^ PowExp := by
      have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
      rw [div_add' _ _ _ hBpos.ne', div_le_iff₀ hBpos]
      linarith
    have hLJ' : (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (LJ_ub : ℝ) * (2 : ℝ) ^ H := by
      rw [hbl, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hLJ (by positivity)
    calc cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
            (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
            ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)
        ≤ ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H + (LJ_ub : ℝ) * (2 : ℝ) ^ H :=
          add_le_add le_rfl hLJ'
      _ = ((Cd : ℝ) / (B : ℝ) + (LJ_ub : ℝ)) * (2 : ℝ) ^ H := by ring
      _ ≤ (2 : ℝ) ^ PowExp * (2 : ℝ) ^ H :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
  have hεα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
      (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
          (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) /
      ((Goldilocks.order : ℝ) ^ 3) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hcr : ((Fri.claimRefs params.logBlowup shape).length : ℝ) * (2 : ℝ) ^ H ≤
        (2 : ℝ) ^ ClaimExp := by exact_mod_cast hclaims
    have hpow63 : (2 : ℝ) ^ (ClaimExp + PowExp) ≤ (2 : ℝ) ^ 63 := by
      exact_mod_cast Nat.pow_le_pow_right two_pos hClaimExp
    have hnum : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
            (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) ≤ (2 : ℝ) ^ 63 := by
      calc _ ≤ ((Fri.claimRefs params.logBlowup shape).length : ℝ) * ((2 : ℝ) ^ PowExp * (2 : ℝ) ^ H) :=
            mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg _)
        _ = (((Fri.claimRefs params.logBlowup shape).length : ℝ) * (2 : ℝ) ^ H) * (2 : ℝ) ^ PowExp := by ring
        _ ≤ (2 : ℝ) ^ ClaimExp * (2 : ℝ) ^ PowExp :=
            mul_le_mul_of_nonneg_right hcr (by positivity)
        _ = (2 : ℝ) ^ (ClaimExp + PowExp) := (pow_add _ _ _).symm
        _ ≤ (2 : ℝ) ^ 63 := hpow63
    exact (div_le_div_of_nonneg_right hnum (by positivity)).trans h63
  have hεβ : (2 * cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
          (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) /
      ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hLJ_nn : 0 ≤ (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) := by
      have hnum_nn : 0 ≤ (p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup := by
        have h1 : ((p : ℝ) / q) ^ 2 ≤ (p : ℝ) / q := by nlinarith
        linarith
      have hden_pos : 0 < ((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup := sub_pos.mpr hgap
      have h1m : 0 ≤ 1 - (p : ℝ) / q := sub_nonneg.mpr hθ1
      positivity
    have hnum : 2 * cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (2 : ℝ) ^ 63 := by
      have h2H : (2 : ℝ) ^ (H + PowExp + 1) ≤ (2 : ℝ) ^ 63 := by
        exact_mod_cast Nat.pow_le_pow_right two_pos (show H + PowExp + 1 ≤ 63 by omega)
      calc 2 * cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
              (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
              ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)
          ≤ 2 * (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
              (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
              ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) := by linarith
        _ ≤ 2 * ((2 : ℝ) ^ PowExp * (2 : ℝ) ^ H) := mul_le_mul_of_nonneg_left hcomb (by norm_num)
        _ = (2 : ℝ) ^ (H + PowExp + 1) := by
            rw [pow_succ', pow_add]; ring
        _ ≤ (2 : ℝ) ^ 63 := h2H
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ params.commitPowBits := by
      exact_mod_cast Nat.one_le_pow params.commitPowBits 2 two_pos
    exact (div_le_self (by positivity) hpow1).trans
      ((div_le_div_of_nonneg_right hnum (by positivity)).trans h63)
  have hmain := goldilocksExt3_soundness_sponge_blake2b512_johnson params shape (hmax.trans hmax32)
    hheight s₀ curveListCA_fp3 hθ0 hθ1 hgap hcT0 hT
    (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128) hεα hεβ hq hadv attempt
  dsimp only at hmain
  have hcol := digest64_sponge_collision_le_quarter_128 (N := N) hN
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at hcol
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rw [← hNcast] at hmain
  refine hmain.trans ?_
  calc (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add le_rfl hcol
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-! ### 4 Concrete 100% Unconditional 128-Bit Johnson Soundness Theorems (`lb = 2, 3, 4`) -/

/-- **100% UNCONDITIONAL 128-Bit Johnson Soundness (`lb = 2, q ≥ 128, queryPow = 20`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` executable `Fri.verify` soundness
over `GoldilocksExt3` with 64B RFC 7693 `BLAKE2b-512` (`Digest64`, 512-bit internal state)
and incremental sponge chaining (`c = 3 / 2`), at agreement threshold `θ = 71 / 128`,
for all `logMaxHeight ≤ 32`, `claimRefs.length * 2 ^ logMaxHeight ≤ 2 ^ 36`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 128 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 36)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (71 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundness_sponge_blake2b512_johnson_of_profile
      2 71 128 9 28 3 27 32 36 params shape hbl (by decide) hmax le_rfl hheight hclaims
      (by rw [hqpow]; exact johnson_71_128_ge_128_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% UNCONDITIONAL 128-Bit Johnson Soundness (`lb = 2, q ≥ 118, queryPow = 20`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` executable `Fri.verify` soundness
with 64B `BLAKE2b-512` covering `q = 118..128` at agreement threshold `θ = 135 / 256`,
for all `logMaxHeight ≤ 30`, `claimRefs.length * 2 ^ logMaxHeight ≤ 2 ^ 31`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 118 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 30)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 31)
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
        ClaimsFail P.ldt P.shift (135 / 256)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundness_sponge_blake2b512_johnson_of_profile
      2 135 256 18 50 5 32 30 31 params shape hbl (by decide) hmax (by decide) hheight hclaims
      (by rw [hqpow]; exact johnson_135_256_ge_118_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% UNCONDITIONAL 128-Bit Native STARK Shrinker Johnson Soundness
(`lb = 3, q ≥ 78, queryPow = 20`, `BLAKE2b-512`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` executable `Fri.verify` soundness
at agreement threshold `θ = 19 / 50`, for all `logMaxHeight ≤ 31`,
`claimRefs.length * 2 ^ logMaxHeight ≤ 2 ^ 32`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 3) (hqn : 78 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
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
        ClaimsFail P.ldt P.shift (19 / 50)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundness_sponge_blake2b512_johnson_of_profile
      3 19 50 13 51 9 31 31 32 params shape hbl (by decide) hmax (by decide) hheight hclaims
      (by rw [hqpow]; exact johnson_19_50_ge_78_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% UNCONDITIONAL 128-Bit Native STARK Shrinker Johnson Soundness
(`lb = 4, q ≥ 58, queryPow = 20`, `BLAKE2b-512`):**
ZERO `CurveListCA` hypothesis! Literal `≤ N / 2 ^ 128` executable `Fri.verify` soundness
at agreement threshold `θ = 35 / 128`, for all `logMaxHeight ≤ 32`,
`claimRefs.length * 2 ^ logMaxHeight ≤ 2 ^ 33`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 4) (hqn : 58 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (35 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundness_sponge_blake2b512_johnson_of_profile
      4 35 128 11 58 13 30 32 33 params shape hbl (by decide) hmax le_rfl hheight hclaims
      (by rw [hqpow]; exact johnson_35_128_ge_58_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

end CertiFri.P3.Exec
