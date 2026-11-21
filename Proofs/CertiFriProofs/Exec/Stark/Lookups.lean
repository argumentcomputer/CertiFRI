import CertiFriProofs.Exec.Stark.SoundnessBatch
import CertiFriProofs.Exec.Stark.Meaning

/-!
# The lookup messages of an accepted proof are balanced

`soundness_verify` and `soundness_verifyBatch` say that the constraints of
every circuit hold on every row, the lookup constraints among them, for the
polynomials the committed columns decode to. The lookup constraints only say
that each circuit accumulates its own lookup sum correctly. This file adds what
the verifier's checks on the sums give: the lookup messages of the whole proof
(of the whole batch) are *balanced*.

## The statement

For a system whose lookups read only the fixed and main traces and the row
selectors (`Circuit.LookupsPlain`; its zeros may read anything), the lookup
messages of an attempt are (`allItems`):

* every public claim, with multiplicity one;
* for every active circuit and every row of its trace, every lookup of the
  circuit, with the multiplicity and the arguments its graph computes on the
  values of the decoded fixed and main columns on that row;
* for a batch, the messages of the preamble with their multiplicities.

They are balanced (`Balanced`, `Theory/Stark/Balance.lean`) when, for every
message, the multiplicities with which it occurs add up to zero in the field.

## Results

* `soundness_verify_lookups`: the probability that `Stark.verify` accepts an
  attempt within the size bounds (`Covered`) whose lookup messages are not
  balanced is at most the bound of `soundness_verify`.
* `soundness_verifyBatch_lookups`: the same for `Stark.verifyBatch`.

## Assumptions

Those of `soundness_verify` and `soundness_verifyBatch` (`sys.HeightOk` among
them; `Covered` and `BatchCovered` are the size bounds alone), and

* the lookups of every circuit of the system are plain
  (`Circuit.LookupsPlain`): their multiplicities and their arguments read only
  the fixed trace, the main trace and the row selectors. The zeros may read
  anything, the lookup trace and the public values included: a system with
  extension constraints is covered, as long as the nodes its lookups refer to
  come before the first node that reads the lookup trace or a public value;
* the characteristic is not two.

"Balanced" is in the field: a multiplicity that is a multiple of the
characteristic counts as zero, and two messages that differ by trailing zeros
are the same message. Bounding the multiplicities is the application's
business.

## Proof

The probability part is that of `soundness_verify` and `soundness_verifyBatch`:
the final log is good except with the probability of the bound. In a good log
the messages of an accepted attempt within the size bounds are balanced
(`lookupsBalanced_of_goodLog`, `batchLookupsBalanced_of_goodLog`):

* If they were not, `balPoly` of them would not vanish at the lookup challenges
  of the run (`verify_good`, `verifyBatch_good`), so no message would have a
  zero denominator there and their lookup sum would not be zero
  (`of_eval_balPoly_ne_zero`).
* No constraint of a shard fails, so the lookup sum leaving its last circuit is
  the lookup sum of its public claims plus that of the messages of its circuits
  (`toModel_residual`, by `messagesAccumulator_model` and
  `lookupSum_of_not_constraintFail`; the trace domains exist in the field
  because the shape check bounds the trace heights by `maxLogDegree`). The
  commitments to the main and to the fixed traces are read in the first
  message, so these messages are those of `allItems` for the shard
  (`headerItems_eq`).
* `Stark.verify` checks that this sum is zero. `Stark.verifyBatch` checks that
  the sums of the shards and the lookup sum of the messages of the batch add up
  to zero (`sums_of_batchAccepts`, `toModel_foldl_residual`). Either way the
  lookup sum of all messages is zero.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr OracleComp
  Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ} (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (B : Bounds)

/-- The preamble of an attempt against `Stark.verify`: one shard with the
header of the proof and the public claims, and no message. -/
def SAttempt.preamble (a : SAttempt F EF D) : BatchPreamble F D :=
  ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩

/-- **The lookup messages of an attempt against `Stark.verify` are balanced**,
for the polynomials the committed columns decode to against the log `l`. -/
def LookupsBalanced (l : Log (SAns F EF D K slots width)) (a : SAttempt F EF D) : Prop :=
  Balanced (allItems M sys θ
    (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2) a.preamble)

/-- **The lookup messages of a batch are balanced**, for the polynomials the
committed columns decode to against the log `l`. -/
def BatchLookupsBalanced (l : Log (SAns F EF D K slots width)) (a : BAttempt F EF D) : Prop :=
  Balanced (allItems M sys θ
    (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
      (committedRow l)).2) a.preamble)

/-! ## The messages of one shard -/

section Shard

variable {M sys θ}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq F] [DecidableEq EF] in
/-- A digest that is read in a message is read with the rows it commits to. -/
private theorem readMsg_snd_eq {m : RawMsg F EF D} (c : Compiled.Committed K D) {root : D}
    (h : root ∈ digestsOf B m) : (readMsg B m c).2 root = c root :=
  ite_eq_left h

omit [DecidableEq K] [Inhabited D] [DecidableEq F] [DecidableEq EF] in
/-- The base-field rows under a digest that is read in a message are those of
the rows it commits to. -/
private theorem baseRows_readMsg (M : StarkModel F EF K) {m : RawMsg F EF D}
    (c : Compiled.Committed K D) {root : D} (h : root ∈ digestsOf B m) :
    M.baseRows (readMsg B m c).2 root = M.baseRows c root := by
  funext dims mi i
  unfold StarkModel.baseRows
  rw [readMsg_snd_eq B c h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The polynomial a column under a root decodes to only depends on the
committed rows under that root. -/
private theorem colPoly_congr_root (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ)
    {com com' : Compiled.Committed K D} {root : D} (h : com root = com' root)
    (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord
  rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The row of a circuit on row `r` of its trace domain, for the committed rows
`com`, agrees with `plainRow` for the committed rows `com'` on the fixed trace,
the main trace and the selectors, when `com` and `com'` have the same rows under
the commitments to the main traces and to the fixed traces. -/
private theorem rowAgree_plainRow_of_congr {com com' : Compiled.Committed K D}
    (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (h1 : com stage1 = com' stage1)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root)
    (publics : Array K) (pos ci r : ℕ) :
    RowAgree
      (pointRow (sys.circuits.getD ci default) (2 ^ logDegrees.getD pos 0)
        (M.gen (logDegrees.getD pos 0))
        (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics
        (M.gen (logDegrees.getD pos 0) ^ r))
      (plainRow M sys θ com' active logDegrees stage1 pos ci r) := by
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage1 stage1 pos ci).main :=
    funext fun j => colPoly_congr_root M _ _ h1 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage1 stage1 pos ci).pre := by
    funext j
    unfold shardCols
    dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congr_root M _ _ (h3 root hpc) _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).preprocessedWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r)) hpre
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).preprocessedWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r * M.gen (logDegrees.getD pos 0)))
      hpre
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).mainWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r)) hmain
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).mainWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r * M.gen (logDegrees.getD pos 0)))
      hmain

omit [FieldOps F] [TwoAdicOps F] [DecidableEq K] [DecidableEq F] in
/-- The messages of a circuit with plain lookups are the same on rows that
agree on the fixed trace, the main trace and the selectors. -/
private theorem circuitItems_congr_of_rowAgree (ι : F → K) {c : Circuit F}
    (hplain : c.LookupsPlain) {rows rows' : ℕ → RowValues K}
    (h : ∀ r, RowAgree (rows r) (rows' r)) (n : ℕ) :
    circuitItems ι c rows n = circuitItems ι c rows' n := by
  obtain ⟨k, hnodes, hlookups⟩ := hplain
  rw [circuitItems, circuitItems]
  refine List.flatMap_congr fun r _ => List.map_congr_left fun l hl => ?_
  obtain ⟨hm, hargs⟩ := hlookups l (Array.mem_toList_iff.mp hl)
  rw [getD_sweep_congr_of_plain ι _ k hnodes (h r) hm]
  refine congrArg _ (List.map_congr_left fun a ha => ?_)
  exact getD_sweep_congr_of_plain ι _ k hnodes (h r) (hargs a (Array.mem_toList_iff.mp ha))

omit [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- **The lookup messages of a shard of circuits with plain lookups**: its
public claims, each with multiplicity one, then `shardLookupItems`, for any
committed rows `com'` with the same rows as `com` under the commitments to the
main traces and to the fixed traces. -/
private theorem headerItems_eq {com com' : Compiled.Committed K D} {h : ShardHeader F D}
    (hplain : ∀ p ∈ (activeIndices h.active).zipIdx,
      (sys.circuits.getD p.1 default).LookupsPlain)
    (h1 : com h.stage1Commit = com' h.stage1Commit)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    headerItems M sys θ com h =
      (h.claims.toList.map fun c => ((1 : K), c.toList.map M.base.toModel)) ++
        shardLookupItems M sys θ com' h.active h.logDegrees h.stage1Commit := by
  rw [headerItems, shardLookupItems]
  refine congrArg _ (List.flatMap_congr fun p hp => ?_)
  exact circuitItems_congr_of_rowAgree M.base.toModel (hplain p hp)
    (fun r => rowAgree_plainRow_of_congr h.active h.logDegrees h.stage1Commit default default
      h1 h3 #[] p.2 p.1 r) _

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] in
/-- An active circuit of a bitmap with one bit per circuit is a circuit of the
system. -/
private theorem getD_mem_circuits_of_active {active : Array Bool}
    (hsize : active.size = sys.circuits.size) {p : ℕ × ℕ}
    (hp : p ∈ (activeIndices active).zipIdx) : sys.circuits.getD p.1 default ∈ sys.circuits := by
  have hmem : p.1 ∈ activeIndices active :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have hlt : p.1 < sys.circuits.size := by
    rw [← hsize]
    exact List.mem_range.mp (List.mem_filter.mp hmem).1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  exact Array.getElem_mem hlt

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- What the shape check says about the sizes: the bitmap has one bit per
circuit, some circuit is active, and there is one lookup sum per active
circuit. -/
private theorem sizes_of_shapeOk {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (hshape : Stark.shapeOk sys proof = true) :
    proof.active.size = sys.circuits.size ∧ 0 < (activeIndices proof.active).length ∧
      proof.intermediateAccumulators.size = (activeIndices proof.active).length := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, hact⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, haccs⟩, -⟩, -⟩ := hshape
  refine ⟨hsize, List.length_pos_iff.mpr fun hnil => ?_, haccs⟩
  rw [hnil] at hact
  cases hact

omit [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- **The residual of a shard is the lookup sum of its messages.** Take a proof
that passes the shape check, with the header `hdr`, for a system whose lookups
are plain and whose largest trace domain exists in the field. If no public
claim has a zero denominator, no constraint of the proof fails for the
committed rows `com`, and no lookup message of the shard has a zero denominator
at the lookup challenges, then the lookup sum leaving the last circuit is the
lookup sum of the messages of the shard. The messages are read off any
committed rows `com'` with the same rows as `com` under the commitments to the
main traces and to the fixed traces. -/
private theorem toModel_residual (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain)
    (h2 : (2 : K) ≠ 0)
    {com com' : Compiled.Committed K D} {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} {hdr : ShardHeader F D}
    (hshape : Stark.shapeOk sys proof = true) (hactive : hdr.active = proof.active)
    (hstage1 : hdr.stage1Commit = proof.stage1Commit) (hlogs : hdr.logDegrees = proof.logDegrees)
    (h1 : com' proof.stage1Commit = com proof.stage1Commit)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com' root = com root)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    {β γ : EF} (hclaims : (claimsAccumulator β γ hdr.claims).1 = true)
    (hfail : ¬ ConstraintFail M sys θ com proof.active proof.logDegrees proof.stage1Commit
      proof.stage2Commit proof.quotientCommit (M.ext.toModel β) (M.ext.toModel γ)
      (M.ext.toModel (claimsAccumulator β γ hdr.claims).2)
      (proof.intermediateAccumulators.map M.ext.toModel))
    (hne : ∀ it ∈ headerItems M sys θ com' hdr,
      M.ext.toModel β + (fpPoly it.2).eval (M.ext.toModel γ) ≠ 0) :
    M.ext.toModel (Stark.residual proof) =
      lookupSum (M.ext.toModel β) (M.ext.toModel γ) (headerItems M sys θ com' hdr) := by
  obtain ⟨hsize, hact, haccs⟩ := sizes_of_shapeOk hshape
  obtain ⟨act, stage1, logs, claims⟩ := hdr
  dsimp only at hactive hstage1 hlogs hclaims hfail
  subst hactive hstage1 hlogs
  have hpl : ∀ p ∈ (activeIndices proof.active).zipIdx,
      (sys.circuits.getD p.1 default).LookupsPlain := fun p hp =>
    hplain _ (getD_mem_circuits_of_active hsize hp)
  rw [headerItems_eq (h := ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩) hpl h1
    h3] at hne ⊢
  -- The claims.
  obtain ⟨-, hcl⟩ := messagesAccumulator_model M β γ _ hclaims
  have hmap : ((claims.toList.map fun claim => (claim, (1 : F))).map fun msg =>
      (M.base.toModel msg.2, msg.1.toList.map M.base.toModel)) =
      claims.toList.map fun c => ((1 : K), c.toList.map M.base.toModel) := by
    rw [List.map_map]
    refine List.map_congr_left fun c _ => ?_
    show (M.base.toModel 1, _) = _
    rw [M.base.map_one]
  rw [hmap] at hcl
  -- The circuits.
  have hsum := lookupSum_of_not_constraintFail h2 hfail hpl
    (fun p hp => (logDegree_le_of_shapeOk hshape hp).trans htwo)
    (by rw [Array.size_map]; exact haccs) fun it hit => hne it (List.mem_append_right _ hit)
  -- The last lookup sum.
  have hlast : (proof.intermediateAccumulators.map M.ext.toModel).back?.getD
      (M.ext.toModel (claimsAccumulator β γ claims).2) =
      M.ext.toModel (Stark.residual proof) := by
    rw [Stark.residual, Array.back?_eq_getElem?, Array.back?_eq_getElem?, Array.size_map,
      Array.getElem?_map, Array.getElem?_eq_getElem (by omega)]
    rfl
  rw [lookupSum_append, ← hcl, ← hlast, hsum]
  rfl

end Shard

/-! ## One proof -/

/-- **In a good log, the lookup messages of an accepted and covered attempt are
balanced.** Take a system whose lookups are plain over a field of
characteristic not two, a good log that holds the queries of the verification
of the attempt, and an answer function that agrees with it. If `Stark.verify`
accepts the attempt against the function and the attempt is covered (its public
claims are within the size bounds), its lookup messages are balanced: otherwise
`balPoly` would not vanish at the lookup challenges (`verify_good`), so the
lookup sum of the messages would not be zero; but it is the lookup sum leaving
the last circuit, which the verifier checks to be zero. -/
private theorem lookupsBalanced_of_goodLog (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain)
    (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys (singleVariant sys B) θ B (maxRounds F) l)
    {f : ∀ x, SAns F EF D K slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : SAttempt F EF D) {l₀ : Log (SAns F EF D K slots width)} {b : Bool}
    (hout : Outcome (shardComp M sys a.proof (firstMessage sys a.proof a.claims) []) l₀ b l)
    (hacc : verifyAccepts M sys f a = true) (hcov : Covered B a) :
    LookupsBalanced M sys θ B l a := by
  obtain ⟨hviol, hbal⟩ :=
    verify_good M sys θ B hfixed hheightOk hshards hN hcast hθ hgood hf a hout hacc hcov
  by_contra hnb
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  simp only [verifyAccepts, Stark.verify, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, hres⟩, hclaims, -⟩ := hacc
  have hclaims' : (claimsAccumulator (lookupOf M sys f a).1 (lookupOf M sys f a).2
      a.claims).1 = true := hclaims
  -- The messages of the attempt are those of its one shard.
  have hitems : allItems M sys θ
      (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
      ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ =
      headerItems M sys θ
        (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
        ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩ := by
    rw [allItems]
    exact (List.append_nil _).trans (List.flatMap_singleton _ _)
  rw [hitems] at hne hsum
  -- The commitments to the main and the fixed traces are read in the first message.
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards a.proof a.claims
  have hlast := toModel_residual (com := M.baseRows (committedRow l))
    (hdr := ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩)
    (β := (lookupOf M sys f a).1) (γ := (lookupOf M sys f a).2) hplain h2 hshape rfl rfl rfl
    (baseRows_readMsg B M _ (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self))
    (fun root hroot => baseRows_readMsg B M _
      (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
    htwo hclaims' hviol hne
  -- The verifier checked that the last lookup sum is zero.
  exact hsum (hlast.symm.trans (((M.ext.beq_iff _ _).mp hres).trans M.ext.map_zero))

/-- **`Stark.verify` only accepts balanced lookups.** For a system whose
lookups are plain (its zeros may read anything) over a field of characteristic
not two, and none of whose fixed traces is taller than the largest trace it
supports (`hheightOk`), the probability that some answer function that agrees
with the final log makes `Stark.verify` accept an attempt, with public claims
within the size bounds (`Covered`), whose lookup messages are not balanced is
at most the bound of `soundness_verify`, for an agreement `θ` inside the
unique-decoding radius (`hθ`). -/
theorem soundness_verify_lookups [Fintype K] [Fintype D]
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain)
    (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
            (m := hs.params.numClaims)))
        fun _ => εpcs)
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts M sys f (attempt out.1) = true ∧ Covered B (attempt out.1) ∧
          ¬ LookupsBalanced M sys θ B l (attempt out.1))
      (experiment M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLog_le (M := M) (sys := sys) (V := singleVariant sys B) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_experiment M sys hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact hnb (lookupsBalanced_of_goodLog M sys θ B hplain h2 hfixed hheightOk hshards hN hcast hθ
    htwo hgood hf (attempt a) hcomp hacc hcov)

/-! ## A batch -/

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
/-- **What acceptance of a batch says about the lookup sums.** There is a
shard, no message of the batch and no public claim of a shard has a zero
denominator at the shared lookup challenges, and the lookup sum of the messages
of the batch plus the residuals of the shards is zero. -/
private theorem sums_of_batchAccepts {f : ∀ x, SAns F EF D K slots width x}
    {a : BAttempt F EF D} (hacc : batchAccepts M sys f a = true) :
    a.preamble.headers.size ≠ 0 ∧
      (messagesAccumulator (batchLookupOf M sys f a).1 (batchLookupOf M sys f a).2
        (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).1 = true ∧
      (∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (Array (List D)) (Array (List D))),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        (claimsAccumulator (batchLookupOf M sys f a).1 (batchLookupOf M sys f a).2
          hdr.claims).1 = true) ∧
      (a.proofs.foldl (fun total proof => total + Stark.residual proof)
        (messagesAccumulator (batchLookupOf M sys f a).1 (batchLookupOf M sys f a).2
          (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2 == 0) = true := by
  simp only [batchAccepts, Stark.verifyBatch, Bool.and_eq_true, List.all_eq_true, bne_iff_ne,
    ne_eq] at hacc
  obtain ⟨⟨hne, -⟩, ⟨hmsgs, hall⟩, hzero⟩ := hacc
  refine ⟨hne, hmsgs, fun i hdr proof hhdr hproof => ?_, hzero⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOk, Bool.and_eq_true] at h
  exact h.2.1

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- **The sum check of a batch, in the model.** If the residual of the proof at
every position is the lookup sum of the messages `g` of the header at that
position, then adding the residuals of the proofs to `init` adds the lookup sum
of the messages of all headers. -/
private theorem toModel_foldl_residual {InputProof CommitProof : Type} (β γ : K)
    (g : ShardHeader F D → List (K × List K)) (hs : List (ShardHeader F D))
    (ps : List (Proof F EF D InputProof CommitProof)) (hlen : hs.length = ps.length)
    (h : ∀ (i : ℕ) (hdr : ShardHeader F D) (proof : Proof F EF D InputProof CommitProof),
      hs[i]? = some hdr → ps[i]? = some proof →
      M.ext.toModel (Stark.residual proof) = lookupSum β γ (g hdr)) (init : EF) :
    M.ext.toModel (ps.foldl (fun total proof => total + Stark.residual proof) init) =
      M.ext.toModel init + lookupSum β γ (hs.flatMap g) := by
  induction hs generalizing ps init with
  | nil =>
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact (add_zero _).symm
  | cons hd hs ih =>
    cases ps with
    | nil => cases hlen
    | cons p ps =>
      rw [List.foldl_cons, ih ps (Nat.succ.inj hlen)
        (fun i hdr proof hh hp => h (i + 1) hdr proof hh hp), M.ext.map_add, h 0 hd p rfl rfl,
        List.flatMap_cons, lookupSum_append, add_assoc]

/-- **In a good log, the lookup messages of an accepted and covered batch are
balanced.** Take a system whose lookups are plain over a field of
characteristic not two, a good log that holds the queries of the verification
of the first `B.shards` shards of the batch, and an answer function that agrees
with it. If `Stark.verifyBatch` accepts the batch against the function and the
batch is covered (its preamble is within the size bounds), its lookup messages
are balanced: otherwise `balPoly` would not vanish at the shared lookup
challenges (`verifyBatch_good`), so the lookup sum of the messages would not be
zero; but it is the lookup sum of the messages of the batch plus the residuals
of the shards, which the verifier checks to be zero. -/
private theorem batchLookupsBalanced_of_goodLog
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain)
    (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, SAns F EF D K slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttempt F EF D) {l₀ : Log (SAns F EF D K slots width)} {b : Bool}
    (hout : Outcome (shardsComp M sys (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchAccepts M sys f a = true) (hcov : BatchCovered B a) :
    BatchLookupsBalanced M sys θ B l a := by
  by_contra hnb
  obtain ⟨hsz, hall⟩ := shardOk_of_batchAccepts M sys hacc
  obtain ⟨hne0, hmsgs, hclaims, hzero⟩ := sums_of_batchAccepts M sys hacc
  have hshardGood := fun {i : ℕ} {hdr : ShardHeader F D}
      {proof : Proof F EF D (Array (List D)) (Array (List D))}
      (hhdr : a.preamble.headers[i]? = some hdr) (hproof : a.proofs[i]? = some proof) =>
    verifyBatch_good M sys θ B hfixed hheightOk hN hcast hθ hgood hf a hout hacc hcov hhdr hproof
  -- There is a shard: its chain gives the clause on the lookup challenges.
  have h0 : 0 < a.preamble.headers.size := Nat.pos_of_ne_zero hne0
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero
    ((hshardGood (Array.getElem?_eq_getElem h0) (Array.getElem?_eq_getElem (hsz ▸ h0))).2 hnb)
  -- The commitments to the main and the fixed traces are read in the first message.
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  -- The residual of every shard is the lookup sum of its messages.
  have hshard : ∀ (i : ℕ) (hdr : ShardHeader F D)
      (proof : Proof F EF D (Array (List D)) (Array (List D))),
      a.preamble.headers.toList[i]? = some hdr → a.proofs.toList[i]? = some proof →
      M.ext.toModel (Stark.residual proof) =
        lookupSum (M.ext.toModel (batchLookupOf M sys f a).1)
          (M.ext.toModel (batchLookupOf M sys f a).2)
          (headerItems M sys θ
            (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
              (committedRow l)).2) hdr) := by
    intro i hdr proof hhdr hproof
    rw [Array.getElem?_toList] at hhdr hproof
    obtain ⟨hshape, hactive, hstage1, hlogs, -⟩ := hall i hdr proof hhdr hproof
    have hmem : hdr ∈ a.preamble.headers := Array.mem_of_getElem? hhdr
    refine toModel_residual (com := M.baseRows (committedRow l)) hplain h2 hshape hactive
      hstage1 hlogs (baseRows_readMsg B M _ ?_) (fun root hroot => baseRows_readMsg B M _ ?_)
      htwo (hclaims i hdr proof hhdr hproof) (hshardGood hhdr hproof).1 fun it hit => hne it ?_
    · rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩)
    · rw [hdigs, hroot]
      exact List.mem_append_left _ List.mem_cons_self
    · rw [allItems]
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, hit⟩)
  -- The lookup sum of the messages of the batch.
  have hm : M.ext.toModel (messagesAccumulator (batchLookupOf M sys f a).1
      (batchLookupOf M sys f a).2
      (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2 =
      lookupSum (M.ext.toModel (batchLookupOf M sys f a).1)
        (M.ext.toModel (batchLookupOf M sys f a).2)
        (a.preamble.messages.toList.map fun m =>
          (M.base.toModel m.multiplicity, m.args.toList.map M.base.toModel)) :=
    (messagesAccumulator_model M _ _ _ hmsgs).2.trans (congrArg _ List.map_map)
  -- The verifier checked that the sums add up to zero.
  have hfold := toModel_foldl_residual M _ _ (headerItems M sys θ _)
    a.preamble.headers.toList a.proofs.toList
    (by rw [Array.length_toList, Array.length_toList, hsz]) hshard
    (messagesAccumulator (batchLookupOf M sys f a).1 (batchLookupOf M sys f a).2
      (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2
  refine hsum ?_
  rw [allItems, lookupSum_append, add_comm, ← hm, ← hfold, Array.foldl_toList]
  exact ((M.ext.beq_iff _ _).mp hzero).trans M.ext.map_zero

/-- **`Stark.verifyBatch` only accepts balanced lookups.** For a system whose
lookups are plain (its zeros may read anything) over a field of characteristic
not two, and none of whose fixed traces is taller than the largest trace it
supports (`hheightOk`), the probability that some answer function that agrees
with the final log makes `Stark.verifyBatch` accept a batch, with a preamble
within the size bounds (`BatchCovered`), whose lookup messages are not balanced
is at most the bound of `soundness_verifyBatch`, for an agreement `θ` inside
the unique-decoding radius (`hθ`). -/
theorem soundness_verifyBatch_lookups [Fintype K] [Fintype D]
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
            (m := hs.params.numClaims)))
        fun _ => εpcs)
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchAccepts M sys f (attempt out.1) = true ∧ BatchCovered B (attempt out.1) ∧
          ¬ BatchLookupsBalanced M sys θ B l (attempt out.1))
      (batchExperiment M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLog_le (M := M) (sys := sys) (V := batchVariant sys B N) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_batchExperiment M sys B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact hnb (batchLookupsBalanced_of_goodLog M sys θ B hplain h2 hfixed hheightOk hN hcast hθ
    htwo hgood hf (attempt a) hcomp hacc hcov)

end CertiFri.Exec.Stark
