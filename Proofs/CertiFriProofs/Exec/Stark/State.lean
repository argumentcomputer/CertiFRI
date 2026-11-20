import CertiFriProofs.Exec.Stark.Preamble

/-!
# The state function of the STARK

The STARK verifier, for one proof or for one shard of a batch, runs a
public-coin protocol whose challenges it derives by Fiat–Shamir. This file
defines the *state function* of that protocol: the set of partial transcripts
after which a cheating prover has not yet been lucky. It proves that the state
function is round-by-round sound, and what an accepted transcript that is still
doomed says.

## The rounds

A transcript is a list of messages and a list of challenges, one of each per
round. A message is what the verifier absorbs before a squeeze, together with
the rows its commitments open to (`IMsg`). A challenge is a uniform answer
(`UAns`); rounds `0` to `3` use its field element.

* Round `0`: the first message (the sizes of the system, the commitments to
  the fixed and the main traces, the trace heights and the public claims; for a
  batch, of every shard, and the messages of the batch). Challenge `β`.
* Round `1`: `β`, absorbed back. Challenge `γ`.
* Round `2`: `γ`, the position of the shard in a batch, the commitment to the
  lookup traces and the lookup sum leaving each circuit. Challenge `α`.
* Round `3`: the commitment to the quotients. Challenge `ζ`.
* Round `4`: the opened values. Challenge: that of round `0` of the opening
  protocol (`Theory/PcsRbr.lean`).
* Round `4 + k`: the message of round `k` of the opening protocol.

How the first message is decoded, and which shard a chain is about, depend on
the entry point of the verifier (`Variant`).

## The state function

`sdoomedL msgs chals` holds when, for the preamble `pre` the first message
decodes to, provided it is within the size bounds (`PreOk`):

* if the lookup messages of all shards (`allItems`) are not balanced, then
  `balPoly` does not vanish identically at `β` (from round `1`), nor at `β`
  and `γ` (from round `2`);
* from round `3`, for the shard of the chain, provided its shape is supported
  (`Supported`): if some constraint fails on some row (`ConstraintFail`), then
  after round `3` the folded constraints fail on some row (`AlphaFail`), and
  from round `4` the check at `ζ` fails (`ZetaFail`) and, from round `5`,
  either the executable checks do not pass on any opened values with the
  absorbed flattening (`Check`), or the opening protocol is in its doomed
  state.

## Results

* `sdoomed_nil`: the empty transcript is doomed.
* `rbrSound_sdoomed`: round-by-round soundness, with the errors `roundErr`:
  `2 * itemBound / |K|` for `β`, `2 * itemBound * lenBound / |K|` for `γ`,
  `(constraintBound - 1) / |K|` for `α`, `zetaBound / |K|` for `ζ`, and a
  bound `εpcs` on the errors of the opening protocol for every supported
  shape.
* `balance_of_sdoomedL`: in a doomed transcript of at least two rounds, if the
  lookup messages are not balanced then `balPoly` does not vanish at the
  challenges.
* `good_of_sdoomedL`: in a doomed full transcript on which the executable
  checks pass, the proof-of-work checks pass and the opening protocol accepts,
  no constraint fails.

## How round-by-round soundness is proved

By the number of rounds of the transcript. Rounds `0` and `1` are the two
lookup challenges (`fractionLE_balPoly_beta`, `fractionLE_balPoly_gamma`),
round `2` is the constraint challenge (`fractionLE_alphaFail`), round `3` the
out-of-domain point (`fractionLE_zetaFail`). A later round is a round of the
opening protocol, whose challenge is read off the uniform answer
(`fractionLE_pcsChal`), or it comes after the last round of the opening
protocol and changes nothing. A new round changes what a chain says about its
shard only where the new message or the new challenge is read. The commitment
to the quotients arrives in round `3`: `ConstraintFail` and `AlphaFail` do not
read it, and read the committed rows only under the commitments to the main,
the fixed and the lookup traces, so they are the same before and after.

## Assumptions

* The round-by-round soundness of the opening protocol for every supported
  shape is a hypothesis (`hpcs`); it is proved elsewhere from the proximity
  results.
* `Supported`: the first domain of the opening exists in the field, no
  committed column is shorter than the final height, and the margin of unique
  decoding holds at the height of every committed matrix. Chains about a shard
  of another shape are doomed by definition: the theorems say nothing about
  them.
* `PreOk`: the size bounds `Bounds` on the numbers of shards, claims and
  messages and on their lengths. They enter the errors of the lookup
  challenges.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D]

/-! ## One shard -/

/-- What a chain says about the shard it is about: the header of the shard, the
commitments to its lookup traces and its quotients, the lookup sums, and the
four challenges of the rounds before the opening protocol. -/
structure ShardView (F EF D K : Type) where
  /-- The header of the shard. -/
  hdr : ShardHeader F D
  /-- The commitment to the lookup traces. -/
  stage2 : D
  /-- The commitment to the quotients. -/
  quot : D
  /-- The lookup sum of the public claims, entering the first circuit. -/
  acc0 : EF
  /-- The lookup sum leaving each active circuit. -/
  accs : Array EF
  /-- The first lookup challenge. -/
  β : K
  /-- The second lookup challenge. -/
  γ : K
  /-- The constraint challenge. -/
  α : K
  /-- The out-of-domain point. -/
  ζ : K

section Shard

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ)

/-- The shape of the opening claims of a shard. -/
def ShardView.shape (v : ShardView F EF D K) : ClaimShape :=
  starkShape sys M.extData.d v.hdr.active v.hdr.logDegrees

/-- The shape of a shard is supported: its first domain exists in the field,
no committed column is shorter than the final height, the margin of unique
decoding holds at the height of every committed matrix, its header has one
activation bit per circuit, and its first domain is no larger than the largest
trace the system supports, times the blowup. -/
structure Supported (v : ShardView F EF D K) : Prop where
  /-- The first domain exists in the field. -/
  two : logMaxHeight sys.fri.logBlowup (v.shape M sys) ≤ TwoAdicOps.twoAdicity (F := F)
  /-- No committed column is shorter than the final height. -/
  final : ∀ m ∈ (v.shape M sys).flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup
  /-- The margin of unique decoding. -/
  margin : ∀ m ∈ (v.shape M sys).flatten,
    DecodeMargin (M.coset (m.logDegree + sys.fri.logBlowup)) (2 ^ m.logDegree) θ
  /-- The header has one activation bit per circuit. -/
  active : v.hdr.active.size = sys.circuits.size
  /-- The first domain is no larger than the largest the system supports. -/
  height : logMaxHeight sys.fri.logBlowup (v.shape M sys) ≤
    sys.maxLogDegree + sys.fri.logBlowup

variable {M sys θ}

/-- The parameters of the opening protocol of a shard. -/
noncomputable def Supported.params {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    Compiled.Params K :=
  modelParams M.toFieldModel sys.fri (v.shape M sys) (M.wellFormed sys.fri _ hs.two)

variable (M sys θ)

/-- A representation of an element of the model field. -/
noncomputable def rep (x : K) : EF := Function.surjInv M.surj x

/-- Some constraint of the shard fails on some row, for the committed rows
`com`. -/
def ShardView.CFail (v : ShardView F EF D K) (com : Compiled.Committed K D) : Prop :=
  ConstraintFail M sys θ com v.hdr.active v.hdr.logDegrees v.hdr.stage1Commit v.stage2 v.quot
    v.β v.γ (M.ext.toModel v.acc0) (v.accs.map M.ext.toModel)

/-- The folded constraints of the shard fail on some row. -/
def ShardView.AFail (v : ShardView F EF D K) (com : Compiled.Committed K D) : Prop :=
  AlphaFail M sys θ com v.hdr.active v.hdr.logDegrees v.hdr.stage1Commit v.stage2 v.quot
    v.β v.γ (M.ext.toModel v.acc0) (v.accs.map M.ext.toModel) v.α

/-- The check at the out-of-domain point fails for some circuit of the
shard. -/
def ShardView.ZFail (v : ShardView F EF D K) (com : Compiled.Committed K D) : Prop :=
  ZetaFail M sys θ com v.hdr.active v.hdr.logDegrees v.hdr.stage1Commit v.stage2 v.quot
    v.β v.γ (M.ext.toModel v.acc0) (v.accs.map M.ext.toModel) v.α v.ζ

/-- The commitments of the opening claims of a shard: the main traces, the
lookup traces, the quotients, and the fixed traces if the system has any. -/
def ShardView.commitments (v : ShardView F EF D K) : Array D :=
  #[v.hdr.stage1Commit, v.stage2, v.quot] ++
    match sys.preprocessedCommit with
    | some c => #[c]
    | none => #[]

/-- **The executable checks pass**, for some opened values with the flattening
`values`: there is a proof with the header, the commitments and the lookup sums
of the shard, of the right shape, whose opened values flatten to `values`, and
on which the constraint checks pass for representations of the challenges. -/
def ShardView.Check (v : ShardView F EF D K) (values : Array EF) : Prop :=
  ∃ proof : Proof F EF D Unit Unit,
    proof.active = v.hdr.active ∧ proof.stage1Commit = v.hdr.stage1Commit ∧
    proof.stage2Commit = v.stage2 ∧ proof.quotientCommit = v.quot ∧
    proof.intermediateAccumulators = v.accs ∧ proof.logDegrees = v.hdr.logDegrees ∧
    shapeOk sys proof = true ∧
    claimValues (openingClaims sys proof (rep M v.ζ)) = values ∧
    constraintsOk sys proof (rep M v.β) (rep M v.γ) v.acc0 (rep M v.α) (rep M v.ζ) = true ∧
    zetaOk proof (rep M v.ζ) = true

end Shard

/-! ## The committed rows of a shard -/

/-- The committed rows a chain reads for the commitments of its shard: those of
the message of round `0` for the commitments to the main and the fixed traces,
those of round `2` for the commitment to the lookup traces, and those of round
`3` for any other, which is where the commitment to the quotients is sent. -/
def comOf (sys : System F D) (v : ShardView F EF D K) (msgs : List (IMsg F EF D K)) :
    Compiled.Committed K D := fun root =>
  if root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root then comAt msgs 0 root
  else if root = v.stage2 then comAt msgs 2 root
  else comAt msgs 3 root

/-! ## Reading a transcript with one more round -/

section Append

variable {slots width : ℕ} {msgs : List (IMsg F EF D K)} {chals : List (UAns K slots width)}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- A new message does not change what the verifier absorbed in an earlier
round. -/
private theorem rawAt_append_of_lt (m : IMsg F EF D K) {j : ℕ} (hj : j < msgs.length) :
    rawAt (msgs ++ [m]) j = rawAt msgs j := by
  unfold rawAt
  rw [List.getElem?_append_left hj]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- A new message does not change the committed rows of an earlier round. -/
private theorem comAt_append_of_lt (m : IMsg F EF D K) {j : ℕ} (hj : j < msgs.length) :
    comAt (msgs ++ [m]) j = comAt msgs j := by
  unfold comAt
  rw [List.getElem?_append_left hj]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- What the verifier absorbed in the round of a new message. -/
private theorem rawAt_append_length (msgs : List (IMsg F EF D K)) (m : IMsg F EF D K) :
    rawAt (msgs ++ [m]) msgs.length = m.1 := by
  unfold rawAt
  rw [List.getElem?_concat_length]
  rfl

omit [DecidableEq K] in
/-- A new challenge does not change the answer of an earlier round. -/
private theorem ansAt_append_of_lt (c : UAns K slots width) {j : ℕ} (hj : j < chals.length) :
    ansAt (chals ++ [c]) j = ansAt chals j := by
  unfold ansAt
  rw [List.getElem?_append_left hj]

omit [DecidableEq K] in
/-- The answer of the round of a new challenge. -/
private theorem ansAt_append_length (chals : List (UAns K slots width))
    (c : UAns K slots width) : ansAt (chals ++ [c]) chals.length = c := by
  unfold ansAt
  rw [List.getElem?_concat_length]
  rfl

omit [DecidableEq K] in
/-- A new challenge does not change the field challenge of an earlier round. -/
private theorem fieldAt_append_of_lt (c : UAns K slots width) {j : ℕ} (hj : j < chals.length) :
    fieldAt (chals ++ [c]) j = fieldAt chals j := by
  unfold fieldAt
  rw [ansAt_append_of_lt c hj]

omit [DecidableEq K] in
/-- The field challenge of the round of a new challenge. -/
private theorem fieldAt_append_length (chals : List (UAns K slots width))
    (c : UAns K slots width) : fieldAt (chals ++ [c]) chals.length = c.field := by
  unfold fieldAt
  rw [ansAt_append_length]

omit [DecidableEq K] in
/-- A new challenge does not change the field challenge of a round after its
own: there is none. -/
private theorem fieldAt_append_of_gt (c : UAns K slots width) {j : ℕ} (hj : chals.length < j) :
    fieldAt (chals ++ [c]) j = fieldAt chals j := by
  unfold fieldAt ansAt
  rw [List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega),
    List.getElem?_eq_none (by omega)]

end Append

/-! ## What the events of a shard read of the committed rows -/

section Rows

variable {M : StarkModel F EF K} {sys : System F D} {θ : ℝ} {com com' : Compiled.Committed K D}

omit [DecidableEq K] [Inhabited D] [DecidableEq D] in
/-- The base-field rows under a root only depend on the committed rows under
that root. -/
private theorem baseRows_congr (M : StarkModel F EF K) {root : D} (h : com root = com' root) :
    M.baseRows com root = M.baseRows com' root := by
  funext dims mi i
  unfold StarkModel.baseRows
  rw [h]

omit [Inhabited D] [DecidableEq D] in
/-- The polynomial a column under a root decodes to only depends on the
committed rows under that root. -/
private theorem colPoly_congr (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ) {root : D}
    (h : com root = com' root) (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord
  rw [h]

omit [Inhabited D] [DecidableEq D] in
/-- The row of a circuit at a point does not read the quotient columns, and
reads the committed rows only under the commitments to the main, the lookup and
the fixed traces. -/
private theorem pointRow_shardCols_congr {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} (quot' : D) (h1 : com stage1 = com' stage1)
    (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) (c : Circuit F)
    (n : ℕ) (g : K) (pos ci : ℕ) (publics : Array K) (x : K) :
    pointRow c n g (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics x =
      pointRow c n g (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci)
        publics x := by
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).main :=
    funext fun j => colPoly_congr M _ _ h1 _ _ _ _
  have hstage2 : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).stage2 =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).stage2 :=
    funext fun j => colPoly_congr M _ _ h2 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).pre := by
    funext j
    unfold shardCols
    dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congr M _ _ (h3 root hpc) _ _ _ _
  unfold pointRow
  rw [hmain, hstage2, hpre]

omit [Inhabited D] [DecidableEq D] in
/-- The constraint values of a circuit do not read the quotient columns, and
read the committed rows only under the commitments to the main, the lookup and
the fixed traces. -/
private theorem rowVals_congr {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} (quot' : D) {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs =
      rowVals M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  funext pos ci x
  unfold rowVals
  rw [pointRow_shardCols_congr quot' h1 h2 h3]

omit [Inhabited D] [DecidableEq D] in
/-- Whether a constraint fails does not depend on the commitment to the
quotients, and depends on the committed rows only under the commitments to the
main, the lookup and the fixed traces. -/
private theorem constraintFail_congr {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs ↔
      ConstraintFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  unfold ConstraintFail
  rw [rowVals_congr quot' h1 h2 h3]

omit [Inhabited D] [DecidableEq D] in
/-- Whether the folded constraints fail does not depend on the commitment to
the quotients, and depends on the committed rows only under the commitments to
the main, the lookup and the fixed traces. -/
private theorem alphaFail_congr {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K} {α : K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    AlphaFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs α ↔
      AlphaFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs α := by
  unfold AlphaFail
  rw [rowVals_congr quot' h1 h2 h3]

end Rows

/-! ## The state function -/

section State

variable {slots width : ℕ} (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D)
  (θ : ℝ) (B : Bounds) (msgs : List (IMsg F EF D K)) (chals : List (UAns K slots width))

/-- What a chain says about the shard with header `hdr`. -/
noncomputable def viewOf (hdr : ShardHeader F D) : ShardView F EF D K where
  hdr := hdr
  stage2 := (digestsIn (rawAt msgs 2)).getD 0 default
  quot := (digestsIn (rawAt msgs 3)).getD 0 default
  acc0 := (claimsAccumulator (rep M (fieldAt chals 0)) (rep M (fieldAt chals 1)) hdr.claims).2
  accs := ((extsOf (rawAt msgs 2)).drop 1).toArray
  β := fieldAt chals 0
  γ := fieldAt chals 1
  α := fieldAt chals 2
  ζ := fieldAt chals 3

/-- The opened values a chain absorbed. -/
def valuesOf : Array EF := (extsOf (rawAt msgs 4)).toArray

variable {M sys θ}

/-- The message of round `k` of the opening protocol of a shard, read off a
chain: the claims about the committed columns for round `0`, the word of the
commitment or of the final polynomial for a later round. -/
noncomputable def pcsMsg {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    ℕ → PcsRbr.Msg K hs.params.numClaims
  | 0 => hs.params.read 0
      (view M.toFieldModel sys.fri (v.shape M sys)
        (firstMessage (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ))
          (valuesOf msgs)))
      (M.baseRows (comOf sys v msgs))
  | k + 1 => hs.params.read (k + 1)
      (view M.toFieldModel sys.fri (v.shape M sys) (rawAt msgs (4 + (k + 1))))
      (comAt msgs (4 + (k + 1)))

/-- The first `j` rounds of the opening protocol of a shard, read off a
chain. -/
noncomputable def pcsT {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    (j : ℕ) → Transcript (PcsRbr.Msg K hs.params.numClaims)
      (GrindChal (powBits sys.fri (v.shape M sys)) (Chal hs.params.ldt hs.params.queries)) j
  | 0 => .nil
  | j + 1 => (pcsT hs j).snoc (pcsMsg msgs hs j)
      (pcsChal hs.params (powBits sys.fri (v.shape M sys)) j (ansAt chals (4 + j)))

/-- The opening protocol of a shard is in its doomed state after the rounds a
chain holds of it. -/
def PcsDoomed {v : ShardView F EF D K} (hs : Supported M sys θ v) : Prop :=
  grindDoomed (powBits sys.fri (v.shape M sys))
    (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries)
    (min (msgs.length - 4) (hs.params.rounds + 2))
    (pcsT msgs chals hs (min (msgs.length - 4) (hs.params.rounds + 2)))

/-- The part of the state function about one shard, for a chain of at least
three rounds. -/
def shardDoomed {v : ShardView F EF D K} (hs : Supported M sys θ v) : Prop :=
  v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
    (msgs.length = 3 → v.AFail M sys θ (M.baseRows (comOf sys v msgs))) ∧
    (4 ≤ msgs.length → v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧
      (5 ≤ msgs.length → v.Check M sys (valuesOf msgs) → PcsDoomed msgs chals hs))

variable (M sys θ)

/-- **The state function**, on the messages and the challenges of a
transcript. -/
def sdoomedL : Prop :=
  ∀ pre, V.dec0 (rawAt msgs 0) = some pre → PreOk sys B pre →
    (¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre) →
      (1 ≤ msgs.length →
        (balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
          (C (fieldAt chals 0)) ≠ 0) ∧
      (2 ≤ msgs.length →
        ((balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
          (C (fieldAt chals 0))).eval (fieldAt chals 1) ≠ 0)) ∧
    (3 ≤ msgs.length → ∀ hdr, pre.headers[V.shard (rawAt msgs 2)]? = some hdr →
      ∀ hs : Supported M sys θ (viewOf M msgs chals hdr), shardDoomed msgs chals hs)

/-- The challenges of a transcript, first round first. -/
def chalsOf {Msg U : Type} : {i : ℕ} → Transcript Msg (fun _ => U) i → List U
  | _, .nil => []
  | _, .snoc t _ c => chalsOf t ++ [c]

/-- **The state function of the STARK.** -/
def sdoomed (i : ℕ) (t : Transcript (IMsg F EF D K) (UChal K slots width) i) : Prop :=
  sdoomedL M sys V θ B t.msgs (chalsOf t)

/-- The error of each round: the two lookup challenges, the constraint
challenge, the out-of-domain point, and the rounds of the opening protocol. -/
noncomputable def roundErr [Fintype K] (εpcs : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then (2 * itemBound sys B : ℕ) / Fintype.card K
  else if i = 1 then (2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K
  else if i = 2 then (constraintBound sys M.extData.d - 1 : ℕ) / Fintype.card K
  else if i = 3 then zetaBound sys / Fintype.card K
  else εpcs

variable {M sys V θ B msgs chals}

/-! ### A transcript with one more round: the view and the opening protocol -/

/-- A transcript of `i` rounds has `i` challenges. -/
private theorem length_chalsOf {Msg U : Type} :
    ∀ {i : ℕ} (t : Transcript Msg (fun _ => U) i), (chalsOf t).length = i
  | _, .nil => rfl
  | _, .snoc t _ c => by
    show (chalsOf t ++ [c]).length = _
    rw [List.length_append, length_chalsOf t, List.length_singleton]

omit [DecidableEq K] [DecidableEq D] in
/-- With two earlier challenges, a new challenge is the constraint challenge of
the view. -/
private theorem viewOf_append_two (hdr : ShardHeader F D) (hc : chals.length = 2)
    (c : UAns K slots width) :
    viewOf M msgs (chals ++ [c]) hdr = { viewOf M msgs chals hdr with α := c.field } := by
  have h0 : fieldAt (chals ++ [c]) 0 = fieldAt chals 0 := fieldAt_append_of_lt c (by omega)
  have h1 : fieldAt (chals ++ [c]) 1 = fieldAt chals 1 := fieldAt_append_of_lt c (by omega)
  have h2 : fieldAt (chals ++ [c]) 2 = c.field := by
    have h := fieldAt_append_length chals c
    rwa [hc] at h
  have h3 : fieldAt (chals ++ [c]) 3 = fieldAt chals 3 := fieldAt_append_of_gt c (by omega)
  simp only [viewOf, h0, h1, h2, h3]

omit [DecidableEq K] [DecidableEq D] in
/-- With three earlier rounds, a new round gives the view its commitment to the
quotients and its out-of-domain point. -/
private theorem viewOf_append_three (hdr : ShardHeader F D) (hm : msgs.length = 3)
    (hc : chals.length = 3) (m : IMsg F EF D K) (c : UAns K slots width) :
    viewOf M (msgs ++ [m]) (chals ++ [c]) hdr =
      { viewOf M msgs chals hdr with quot := (digestsIn m.1).getD 0 default, ζ := c.field } := by
  have r2 : rawAt (msgs ++ [m]) 2 = rawAt msgs 2 := rawAt_append_of_lt m (by omega)
  have r3 : rawAt (msgs ++ [m]) 3 = m.1 := by
    have h := rawAt_append_length msgs m
    rwa [hm] at h
  have h0 : fieldAt (chals ++ [c]) 0 = fieldAt chals 0 := fieldAt_append_of_lt c (by omega)
  have h1 : fieldAt (chals ++ [c]) 1 = fieldAt chals 1 := fieldAt_append_of_lt c (by omega)
  have h2 : fieldAt (chals ++ [c]) 2 = fieldAt chals 2 := fieldAt_append_of_lt c (by omega)
  have h3 : fieldAt (chals ++ [c]) 3 = c.field := by
    have h := fieldAt_append_length chals c
    rwa [hc] at h
  simp only [viewOf, r2, r3, h0, h1, h2, h3]

omit [DecidableEq K] [DecidableEq D] in
/-- With four earlier rounds, a new round does not change the view. -/
private theorem viewOf_append (hdr : ShardHeader F D) (hm : 4 ≤ msgs.length)
    (hc : 4 ≤ chals.length) (m : IMsg F EF D K) (c : UAns K slots width) :
    viewOf M (msgs ++ [m]) (chals ++ [c]) hdr = viewOf M msgs chals hdr := by
  have r2 : rawAt (msgs ++ [m]) 2 = rawAt msgs 2 := rawAt_append_of_lt m (by omega)
  have r3 : rawAt (msgs ++ [m]) 3 = rawAt msgs 3 := rawAt_append_of_lt m (by omega)
  have h0 : fieldAt (chals ++ [c]) 0 = fieldAt chals 0 := fieldAt_append_of_lt c (by omega)
  have h1 : fieldAt (chals ++ [c]) 1 = fieldAt chals 1 := fieldAt_append_of_lt c (by omega)
  have h2 : fieldAt (chals ++ [c]) 2 = fieldAt chals 2 := fieldAt_append_of_lt c (by omega)
  have h3 : fieldAt (chals ++ [c]) 3 = fieldAt chals 3 := fieldAt_append_of_lt c (by omega)
  simp only [viewOf, r2, r3, h0, h1, h2, h3]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- With five earlier rounds, a new round does not change the opened values. -/
private theorem valuesOf_append (hm : 5 ≤ msgs.length) (m : IMsg F EF D K) :
    valuesOf (msgs ++ [m]) = valuesOf msgs := by
  unfold valuesOf
  rw [rawAt_append_of_lt m (by omega)]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] in
/-- With four earlier rounds, a new round does not change the committed rows of
a shard. -/
private theorem comOf_append (sys : System F D) (v : ShardView F EF D K) (hm : 4 ≤ msgs.length)
    (m : IMsg F EF D K) : comOf sys v (msgs ++ [m]) = comOf sys v msgs := by
  unfold comOf
  rw [comAt_append_of_lt m (show 0 < msgs.length by omega),
    comAt_append_of_lt m (show 2 < msgs.length by omega),
    comAt_append_of_lt m (show 3 < msgs.length by omega)]

omit [DecidableEq K] [Inhabited D] in
/-- With three earlier rounds, a new round does not change the base-field rows
under the commitments to the main, the fixed and the lookup traces. -/
private theorem baseRows_comOf_append (M : StarkModel F EF K) (sys : System F D)
    (v : ShardView F EF D K) (hm : 3 ≤ msgs.length) (m : IMsg F EF D K) {root : D}
    (hroot : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root ∨ root = v.stage2) :
    M.baseRows (comOf sys v (msgs ++ [m])) root = M.baseRows (comOf sys v msgs) root := by
  refine baseRows_congr M ?_
  unfold comOf
  rw [comAt_append_of_lt m (show 0 < msgs.length by omega),
    comAt_append_of_lt m (show 2 < msgs.length by omega)]
  by_cases h1 : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root
  · rw [ite_eq_left h1, ite_eq_left h1]
  · have h2 : root = v.stage2 := by tauto
    rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]

/-- A new round does not change the message of an earlier round of the opening
protocol. -/
private theorem pcsMsg_append {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (m : IMsg F EF D K) {k : ℕ} (hk : 4 + k < msgs.length) :
    pcsMsg (msgs ++ [m]) hs k = pcsMsg msgs hs k := by
  rcases k with _ | k
  · simp only [pcsMsg, valuesOf_append (show 5 ≤ msgs.length by omega) m,
      comOf_append sys v (show 4 ≤ msgs.length by omega) m]
  · simp only [pcsMsg, rawAt_append_of_lt m hk, comAt_append_of_lt m hk]

/-- A new round does not change the earlier rounds of the opening protocol. -/
private theorem pcsT_append {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (m : IMsg F EF D K) (c : UAns K slots width) :
    ∀ j, 4 + j ≤ msgs.length → 4 + j ≤ chals.length →
      pcsT (msgs ++ [m]) (chals ++ [c]) hs j = pcsT msgs chals hs j
  | 0, _, _ => rfl
  | j + 1, hm, hc => by
    simp only [pcsT, pcsT_append hs m c j (by omega) (by omega),
      pcsMsg_append hs m (show 4 + j < msgs.length by omega),
      ansAt_append_of_lt c (show 4 + j < chals.length by omega)]

/-- The round of the opening protocol that a new round adds. -/
private theorem pcsT_append_succ {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (m : IMsg F EF D K) (c : UAns K slots width) {j : ℕ} (hm : msgs.length = 4 + j)
    (hc : chals.length = 4 + j) :
    pcsT (msgs ++ [m]) (chals ++ [c]) hs (j + 1) =
      (pcsT msgs chals hs j).snoc (pcsMsg (msgs ++ [m]) hs j)
        (pcsChal hs.params (powBits sys.fri (v.shape M sys)) j c) := by
  have hans : ansAt (chals ++ [c]) (4 + j) = c := by
    have h := ansAt_append_length chals c
    rwa [hc] at h
  simp only [pcsT, pcsT_append (msgs := msgs) (chals := chals) hs m c j (by omega) (by omega),
    hans]

/-- The state of the opening protocol of a shard, for the number of its rounds
that a chain holds. -/
private theorem pcsDoomed_iff {v : ShardView F EF D K} {hs : Supported M sys θ v} {n : ℕ}
    (hn : min (msgs.length - 4) (hs.params.rounds + 2) = n) :
    PcsDoomed msgs chals hs ↔
      grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries) n
        (pcsT msgs chals hs n) := by
  subst hn
  rfl

/-! ### The part of the state function about one shard, by the number of rounds -/

/-- With three rounds, the shard is doomed when a failing constraint makes the
folded constraints fail. -/
private theorem shardDoomed_three {v : ShardView F EF D K} {hs : Supported M sys θ v}
    (hm : msgs.length = 3) :
    shardDoomed msgs chals hs ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.AFail M sys θ (M.baseRows (comOf sys v msgs))) := by
  unfold shardDoomed
  exact ⟨fun h hcf => (h hcf).1 hm,
    fun h hcf => ⟨fun _ => h hcf, fun h4 => absurd h4 (by omega)⟩⟩

/-- With four rounds, the shard is doomed when a failing constraint makes the
check at the out-of-domain point fail. -/
private theorem shardDoomed_four {v : ShardView F EF D K} {hs : Supported M sys θ v}
    (hm : msgs.length = 4) :
    shardDoomed msgs chals hs ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.ZFail M sys θ (M.baseRows (comOf sys v msgs))) := by
  unfold shardDoomed
  exact ⟨fun h hcf => ((h hcf).2 (by omega)).1,
    fun h hcf => ⟨fun h3 => absurd h3 (by omega),
      fun _ => ⟨h hcf, fun h5 => absurd h5 (by omega)⟩⟩⟩

/-- From five rounds on, the shard is doomed when a failing constraint makes
the check at the out-of-domain point fail and, if the executable checks pass,
dooms the opening protocol. -/
private theorem shardDoomed_of_five_le {v : ShardView F EF D K} {hs : Supported M sys θ v}
    (hm : 5 ≤ msgs.length) :
    shardDoomed msgs chals hs ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧
          (v.Check M sys (valuesOf msgs) → PcsDoomed msgs chals hs)) := by
  unfold shardDoomed
  exact ⟨fun h hcf => ⟨((h hcf).2 (by omega)).1, ((h hcf).2 (by omega)).2 hm⟩,
    fun h hcf => ⟨fun h3 => absurd h3 (by omega), fun _ => ⟨(h hcf).1, fun _ => (h hcf).2⟩⟩⟩

/-! ### The rounds -/

/-- **The first lookup challenge.** After the first message, all but a fraction
`2 * itemBound / |K|` of the challenges give a doomed transcript. -/
private theorem fractionLE_beta_round [Fintype K] (m : IMsg F EF D K) :
    FractionLE (fun c : UAns K slots width => ¬ sdoomedL M sys V θ B [m] [c])
      ((2 * itemBound sys B : ℕ) / Fintype.card K) := by
  have h0 : (0 : ℝ) ≤ (2 * itemBound sys B : ℕ) / Fintype.card K := by positivity
  have hnone : FractionLE (fun _ : UAns K slots width => False) _ :=
    FractionLE.false.mono_right h0
  have hraw : rawAt [m] 0 = m.1 := rfl
  rcases hdec : V.dec0 m.1 with _ | pre
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' => ?_
    rw [hraw, hdec] at hdec'
    cases hdec'
  by_cases hgood : PreOk sys B pre ∧ ¬ Balanced (allItems M sys θ (M.baseRows m.2) pre)
  · refine ((fractionLE_field (fractionLE_balPoly_beta hgood.2)).mono_right ?_).mono_left
      fun c hc => ?_
    · exact div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (Nat.mul_le_mul_left 2 (length_allItems_le hgood.1))) (Nat.cast_nonneg _)
    · by_contra hne
      refine hc fun pre' hdec' _ => ?_
      rw [hraw, hdec] at hdec'
      cases hdec'
      exact ⟨fun _ => ⟨fun _ => hne, fun h => absurd h (by simp)⟩, fun h => absurd h (by simp)⟩
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'
    cases hdec'
    exact ⟨fun hb => absurd ⟨hpre', hb⟩ hgood, fun h => absurd h (by simp)⟩

/-- **The second lookup challenge.** From a doomed transcript of one round and
any message, all but a fraction `2 * itemBound * lenBound / |K|` of the
challenges give a doomed transcript. -/
private theorem fractionLE_gamma_round [Fintype K] (hd : sdoomedL M sys V θ B msgs chals)
    (hm : msgs.length = 1) (hc : chals.length = 1) (m : IMsg F EF D K) :
    FractionLE
      (fun c : UAns K slots width => ¬ sdoomedL M sys V θ B (msgs ++ [m]) (chals ++ [c]))
      ((2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K) := by
  have h0 : (0 : ℝ) ≤ (2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K := by
    positivity
  have hnone : FractionLE (fun _ : UAns K slots width => False) _ :=
    FractionLE.false.mono_right h0
  have hraw : rawAt (msgs ++ [m]) 0 = rawAt msgs 0 := rawAt_append_of_lt m (by omega)
  have hcom : comAt (msgs ++ [m]) 0 = comAt msgs 0 := comAt_append_of_lt m (by omega)
  have hlen : (msgs ++ [m]).length = 2 := by rw [List.length_append, hm, List.length_singleton]
  rcases hdec : V.dec0 (rawAt msgs 0) with _ | pre
  · refine hnone.mono_left fun c hc' => hc' fun pre' hdec' => ?_
    rw [hraw, hdec] at hdec'
    cases hdec'
  by_cases hgood : PreOk sys B pre ∧
      ¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)
  · have hβ := ((hd pre hdec hgood.1).1 hgood.2).1 (by omega)
    refine ((fractionLE_field (fractionLE_balPoly_gamma (L := lenBound sys B)
      (length_args_allItems_le hgood.1) hβ)).mono_right ?_).mono_left fun c hc' => ?_
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left 2 (length_allItems_le hgood.1)))) (Nat.cast_nonneg _)
    · by_contra hne
      refine hc' fun pre' hdec' _ => ?_
      rw [hraw, hdec] at hdec'
      cases hdec'
      have h1 : fieldAt (chals ++ [c]) 1 = c.field := by
        have h := fieldAt_append_length chals c
        rwa [hc] at h
      refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [hcom, fieldAt_append_of_lt c (show 0 < chals.length by omega), h1]
      exact fun _ => ⟨fun _ => hβ, fun _ => hne⟩
  · refine hnone.mono_left fun c hc' => hc' fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'
    cases hdec'
    refine ⟨fun hb => ?_, fun h => absurd h (by omega)⟩
    rw [hcom] at hb
    exact absurd ⟨hpre', hb⟩ hgood

/-- From two rounds on, a transcript with one more round is doomed when the
part of the state function about its shard holds: its lookup challenges are
those of the transcript it extends, which is doomed. -/
private theorem sdoomedL_append {pre : BatchPreamble F D}
    (hd : sdoomedL M sys V θ B msgs chals) (hdec : V.dec0 (rawAt msgs 0) = some pre)
    (hpre : PreOk sys B pre) (hm : 2 ≤ msgs.length) (hc : 2 ≤ chals.length)
    (m : IMsg F EF D K) (c : UAns K slots width)
    (h : ∀ hdr, pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? = some hdr →
      ∀ hs : Supported M sys θ (viewOf M (msgs ++ [m]) (chals ++ [c]) hdr),
        shardDoomed (msgs ++ [m]) (chals ++ [c]) hs) :
    sdoomedL M sys V θ B (msgs ++ [m]) (chals ++ [c]) := by
  intro pre' hdec' _
  rw [rawAt_append_of_lt m (show 0 < msgs.length by omega), hdec] at hdec'
  cases hdec'
  refine ⟨?_, fun _ => h⟩
  rw [comAt_append_of_lt m (show 0 < msgs.length by omega),
    fieldAt_append_of_lt c (show 0 < chals.length by omega),
    fieldAt_append_of_lt c (show 1 < chals.length by omega)]
  exact fun hb => ⟨fun _ => ((hd _ hdec hpre).1 hb).1 (by omega),
    fun _ => ((hd _ hdec hpre).1 hb).2 hm⟩

/-- From two rounds on, a bound on the challenges after which the part of the
state function about the shard fails, for the preamble and the header the
messages decode to, is a bound on the challenges that give a transcript that is
not doomed. -/
private theorem fractionLE_of_shard [Fintype K] {ε : ℝ} (h0 : 0 ≤ ε)
    (hd : sdoomedL M sys V θ B msgs chals) (hlen : chals.length = msgs.length)
    (hm : 2 ≤ msgs.length) (m : IMsg F EF D K)
    (h : ∀ pre, V.dec0 (rawAt msgs 0) = some pre → PreOk sys B pre →
      ∀ hdr, pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? = some hdr →
        FractionLE
          (fun c : UAns K slots width =>
            ¬ ∀ hs : Supported M sys θ (viewOf M (msgs ++ [m]) (chals ++ [c]) hdr),
              shardDoomed (msgs ++ [m]) (chals ++ [c]) hs) ε) :
    FractionLE
      (fun c : UAns K slots width => ¬ sdoomedL M sys V θ B (msgs ++ [m]) (chals ++ [c])) ε := by
  have hraw : rawAt (msgs ++ [m]) 0 = rawAt msgs 0 := rawAt_append_of_lt m (by omega)
  have hnone : FractionLE (fun _ : UAns K slots width => False) ε :=
    FractionLE.false.mono_right h0
  rcases hdec : V.dec0 (rawAt msgs 0) with _ | pre
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' => ?_
    rw [hraw, hdec] at hdec'
    cases hdec'
  by_cases hpre : PreOk sys B pre
  swap
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'
    cases hdec'
    exact absurd hpre' hpre
  rcases hh : pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? with _ | hdr
  · refine hnone.mono_left fun c hc => hc ?_
    refine sdoomedL_append hd hdec hpre hm (by omega) m c fun hdr' hh' => ?_
    rw [hh] at hh'
    cases hh'
  · refine (h pre hdec hpre hdr hh).mono_left fun c hc hgood => hc ?_
    refine sdoomedL_append hd hdec hpre hm (by omega) m c fun hdr' hh' => ?_
    rw [hh] at hh'
    cases hh'
    exact hgood

/-- **The constraint challenge.** With three messages, for all but a fraction
`(constraintBound - 1) / |K|` of the challenges the shard is doomed, for the
view whose constraint challenge is the challenge. -/
private theorem fractionLE_alpha_round [Fintype K] {v : ShardView F EF D K}
    (hact : v.hdr.active.size ≤ sys.circuits.size) (hm : msgs.length = 3) :
    FractionLE
      (fun c : UAns K slots width => ¬ ∀ hs : Supported M sys θ { v with α := c.field },
        shardDoomed msgs (chals ++ [c]) hs)
      ((constraintBound sys M.extData.d - 1 : ℕ) / Fintype.card K) := by
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  · refine (fractionLE_field (fractionLE_alphaFail hact hCF)).mono_left
      fun c hc hAF => hc fun hs => ?_
    exact (shardDoomed_three hm).mpr fun _ => hAF
  · refine (FractionLE.false.mono_right (by positivity)).mono_left fun c hc => hc fun hs => ?_
    exact (shardDoomed_three hm).mpr fun hcf => absurd hcf hCF

/-- **The out-of-domain point.** From a doomed shard with three rounds and any
message, for all but a fraction `zetaBound / |K|` of the challenges the shard
is doomed, for the view with the new commitment to the quotients whose
out-of-domain point is the challenge. -/
private theorem fractionLE_zeta_round [Fintype K]
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F)) {v : ShardView F EF D K}
    (hact : v.hdr.active.size ≤ sys.circuits.size)
    (hdeg : ∀ pos, v.hdr.logDegrees.getD pos 0 ≤ sys.maxLogDegree) (hm : msgs.length = 3)
    (m : IMsg F EF D K) (q : D) (hd : ∀ hs : Supported M sys θ v, shardDoomed msgs chals hs) :
    FractionLE
      (fun c : UAns K slots width =>
        ¬ ∀ hs : Supported M sys θ { v with quot := q, ζ := c.field },
          shardDoomed (msgs ++ [m]) (chals ++ [c]) hs)
      (zetaBound sys / Fintype.card K) := by
  have hnone : FractionLE (fun _ : UAns K slots width => False)
      (zetaBound sys / Fintype.card K) :=
    FractionLE.false.mono_right (by positivity)
  have hlen : (msgs ++ [m]).length = 4 := by rw [List.length_append, hm, List.length_singleton]
  have h1 := baseRows_comOf_append M sys v (le_of_eq hm.symm) m (.inl rfl)
  have h2 := baseRows_comOf_append M sys v (le_of_eq hm.symm) m (.inr (.inr rfl))
  have h3 : ∀ root, sys.preprocessedCommit = some root →
      M.baseRows (comOf sys v (msgs ++ [m])) root = M.baseRows (comOf sys v msgs) root :=
    fun root hroot => baseRows_comOf_append M sys v (le_of_eq hm.symm) m (.inr (.inl hroot))
  by_cases hsup : Supported M sys θ v
  swap
  · exact hnone.mono_left fun c hc => hc fun hs =>
      absurd ⟨hs.two, hs.final, hs.margin, hs.active, hs.height⟩ hsup
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  swap
  · refine hnone.mono_left fun c hc => hc fun hs => ?_
    exact (shardDoomed_four hlen).mpr fun hcf =>
      absurd ((constraintFail_congr (quot' := v.quot) h1 h2 h3).mp hcf) hCF
  have hAF := (alphaFail_congr (quot := q) (quot' := v.quot) h1 h2 h3).mpr
    ((shardDoomed_three hm).mp (hd hsup) hCF)
  refine (fractionLE_field (fractionLE_zetaFail hact hdeg htwo hAF)).mono_left
    fun c hc hZF => hc fun hs => ?_
  exact (shardDoomed_four hlen).mpr fun _ => hZF

/-- **The rounds of the opening protocol.** From a doomed shard with at least
four rounds and any message, for all but a fraction `εpcs` of the challenges
the shard is doomed: the new round is a round of the opening protocol, which is
round-by-round sound, or it comes after its last round and changes nothing. -/
private theorem fractionLE_pcs_round [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {v : ShardView F EF D K}
    (hs : Supported M sys θ v)
    (hpcs : RbrSound (hs.params.rounds + 2)
      (grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
          (m := hs.params.numClaims)))
      fun _ => εpcs)
    (hm : 4 ≤ msgs.length) (hc : chals.length = msgs.length) (m : IMsg F EF D K)
    (hd : shardDoomed msgs chals hs) :
    FractionLE
      (fun c : UAns K slots width => ¬ shardDoomed (msgs ++ [m]) (chals ++ [c]) hs) εpcs := by
  have hnone : FractionLE (fun _ : UAns K slots width => False) εpcs :=
    FractionLE.false.mono_right hεpcs
  have hlen : (msgs ++ [m]).length = msgs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hcom : comOf sys v (msgs ++ [m]) = comOf sys v msgs := comOf_append sys v hm m
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  swap
  · refine hnone.mono_left fun c hc' => hc' fun hcf => ?_
    rw [hcom] at hcf
    exact absurd hcf hCF
  obtain ⟨hZF, hP⟩ := (hd hCF).2 hm
  have hZF' : v.ZFail M sys θ (M.baseRows (comOf sys v (msgs ++ [m]))) := by
    rw [hcom]
    exact hZF
  by_cases hCk : v.Check M sys (valuesOf (msgs ++ [m]))
  swap
  · exact hnone.mono_left fun c hc' => hc' ((shardDoomed_of_five_le (by omega)).mpr
      fun _ => ⟨hZF', fun hck => absurd hck hCk⟩)
  rcases Nat.lt_or_ge (msgs.length - 4) (hs.params.rounds + 2) with hj | hj
  · obtain ⟨j, hj'⟩ : ∃ j, msgs.length = 4 + j := ⟨msgs.length - 4, by omega⟩
    have hdoom : grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries) j
        (pcsT msgs chals hs j) := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact grindDoomed_nil (doomed_zero _ _ _ _ _)
      · have h5 : 5 ≤ msgs.length := by omega
        rw [valuesOf_append h5 m] at hCk
        exact (pcsDoomed_iff (by omega)).mp (hP h5 hCk)
    have hbits : powBits sys.fri (v.shape M sys) j ≤ width := by
      unfold powBits
      split_ifs <;> omega
    have hbound := fractionLE_pcsChal (slots := slots) (width := width) hs.params
      (powBits sys.fri (v.shape M sys)) j hslots hbits (hs.two.trans hwidth)
      (hpcs j (by omega) (pcsT msgs chals hs j) (pcsMsg (msgs ++ [m]) hs j) hdoom)
    refine hbound.mono_left fun c hc' hgd => hc' ?_
    refine (shardDoomed_of_five_le (by omega)).mpr fun _ => ⟨hZF', fun _ => ?_⟩
    refine (pcsDoomed_iff (n := j + 1) (by omega)).mpr ?_
    rw [pcsT_append_succ hs m c hj' (hc.trans hj')]
    exact hgd
  · have h5 : 5 ≤ msgs.length := by omega
    refine hnone.mono_left fun c hc' => hc' ?_
    refine (shardDoomed_of_five_le (by omega)).mpr fun _ => ⟨hZF', fun hck => ?_⟩
    rw [valuesOf_append h5 m] at hck
    refine (pcsDoomed_iff (n := hs.params.rounds + 2) (by omega)).mpr ?_
    rw [pcsT_append hs m c (hs.params.rounds + 2) (by omega) (by omega)]
    exact (pcsDoomed_iff (by omega)).mp (hP h5 hck)

/-- **Round-by-round soundness, on the messages and the challenges of a
transcript.** From a doomed transcript and any message, all but a fraction
`roundErr` of the challenges give a doomed transcript. -/
private theorem fractionLE_sdoomedL [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
            (m := hs.params.numClaims)))
        fun _ => εpcs)
    (hlen : chals.length = msgs.length) (m : IMsg F EF D K)
    (hd : sdoomedL M sys V θ B msgs chals) :
    FractionLE
      (fun c : UAns K slots width => ¬ sdoomedL M sys V θ B (msgs ++ [m]) (chals ++ [c]))
      (roundErr M sys B εpcs msgs.length) := by
  unfold roundErr
  split_ifs with h0 h1 h2 h3
  · obtain rfl : msgs = [] := List.length_eq_zero_iff.mp h0
    obtain rfl : chals = [] := List.length_eq_zero_iff.mp hlen
    exact fractionLE_beta_round m
  · exact fractionLE_gamma_round hd h1 (hlen.trans h1) m
  · refine fractionLE_of_shard (by positivity) hd hlen (by omega) m
      fun pre hdec hpre hdr hh => ?_
    have hok := hpre.header hdr (Array.mem_of_getElem? hh)
    refine (fractionLE_alpha_round (θ := θ) (msgs := msgs ++ [m]) (chals := chals)
      (v := viewOf M (msgs ++ [m]) chals hdr) hok.active.le
      (by rw [List.length_append, h2, List.length_singleton])).mono_left
      fun c hc hgood => hc ?_
    rw [viewOf_append_two hdr (hlen.trans h2) c]
    exact hgood
  · refine fractionLE_of_shard (by positivity) hd hlen (by omega) m
      fun pre hdec hpre hdr hh => ?_
    rw [rawAt_append_of_lt m (by omega)] at hh
    have hok := hpre.header hdr (Array.mem_of_getElem? hh)
    refine (fractionLE_zeta_round htwo (v := viewOf M msgs chals hdr) hok.active.le
      hok.logDegree_le h3 m ((digestsIn m.1).getD 0 default)
      ((hd pre hdec hpre).2 (by omega) hdr hh)).mono_left fun c hc hgood => hc ?_
    rw [viewOf_append_three hdr h3 (hlen.trans h3) m c]
    exact hgood
  · have h4 : 4 ≤ msgs.length := by omega
    refine fractionLE_of_shard hεpcs hd hlen (by omega) m fun pre hdec hpre hdr hh => ?_
    rw [rawAt_append_of_lt m (by omega)] at hh
    have hv := fun c : UAns K slots width =>
      viewOf_append (M := M) (chals := chals) hdr h4 (by omega) m c
    by_cases hsup : Supported M sys θ (viewOf M msgs chals hdr)
    · refine (fractionLE_pcs_round hεpcs hslots hcommit hquery hwidth hsup (hpcs _ hsup) h4
        hlen m ((hd pre hdec hpre).2 (by omega) hdr hh hsup)).mono_left
        fun c hc hgood => hc ?_
      rw [hv c]
      exact fun _ => hgood
    · refine (FractionLE.false.mono_right hεpcs).mono_left fun c hc => hc ?_
      rw [hv c]
      exact fun hs => absurd hs hsup

variable (M sys V θ B msgs chals)

/-- The empty transcript is doomed. -/
theorem sdoomed_nil : sdoomed (slots := slots) (width := width) M sys V θ B 0 .nil :=
  fun _ _ _ => ⟨fun _ => ⟨fun h => (Nat.not_succ_le_zero _ h).elim,
    fun h => (Nat.not_succ_le_zero _ h).elim⟩, fun h => (Nat.not_succ_le_zero _ h).elim⟩

/-- **Round-by-round soundness of the STARK.** The opening protocol of every
supported shard is round-by-round sound with every error at most `εpcs`; the
trace heights the system supports exist in the field; a uniform answer has
more slots than there are queries, and is wide enough for the proof-of-work
bits and for a query index. Then the state function is round-by-round sound for
any number of rounds, with the errors `roundErr`. -/
theorem rbrSound_sdoomed [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
            (m := hs.params.numClaims)))
        fun _ => εpcs)
    (r : ℕ) :
    RbrSound r (sdoomed (slots := slots) (width := width) M sys V θ B)
      (roundErr M sys B εpcs) := by
  intro i _ t m hd
  have h := fractionLE_sdoomedL (V := V) (B := B) hεpcs htwo hslots hcommit hquery hwidth hpcs
    ((length_chalsOf t).trans t.length_msgs.symm) m hd
  rw [t.length_msgs] at h
  exact h

variable {M sys V θ B msgs chals}

/-- In a doomed transcript of at least two rounds whose first message decodes
to a preamble within the size bounds, if the lookup messages are not balanced
then `balPoly` does not vanish at the two lookup challenges. -/
theorem balance_of_sdoomedL (hd : sdoomedL M sys V θ B msgs chals) {pre : BatchPreamble F D}
    (hdec : V.dec0 (rawAt msgs 0) = some pre) (hpre : PreOk sys B pre) (hlen : 2 ≤ msgs.length)
    (hbal : ¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)) :
    ((balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
      (C (fieldAt chals 0))).eval (fieldAt chals 1) ≠ 0 :=
  ((hd pre hdec hpre).1 hbal).2 hlen

/-- The claims of the rounds of the opening protocol that a chain holds are
those of the message of its round `0`. -/
private theorem claimsOf_ungrind_pcsT {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    ∀ j, claimsOf (ungrind (pcsT msgs chals hs (j + 1))) = (pcsMsg msgs hs 0).claims
  | 0 => rfl
  | j + 1 => claimsOf_ungrind_pcsT hs j

omit [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] in
/-- The commitments of the opening claims of a proof with the commitments of a
view are the commitments of the view. -/
private theorem map_commitment_openingClaims (v : ShardView F EF D K)
    (proof : Proof F EF D Unit Unit) (ζ : EF) (h1 : proof.stage1Commit = v.hdr.stage1Commit)
    (h2 : proof.stage2Commit = v.stage2) (h3 : proof.quotientCommit = v.quot) :
    (openingClaims sys proof ζ).map (·.commitment) = v.commitments sys := by
  unfold openingClaims ShardView.commitments
  rw [h1, h2, h3]
  cases sys.preprocessedCommit <;> simp

/-- **Passing checks and a failing check at `ζ` make the claims of round `0`
fail.** If the executable checks pass on the opened values a chain absorbed
although the check at the out-of-domain point fails for the polynomials the
committed columns decode to, then the claims of the message of round `0` of the
opening protocol, read off the chain, fail. -/
private theorem claimsFail_pcsMsg (hfixed : sys.FixedOk) {v : ShardView F EF D K}
    (hs : Supported M sys θ v) (hcheck : v.Check M sys (valuesOf msgs))
    (hZF : v.ZFail M sys θ (M.baseRows (comOf sys v msgs))) :
    ClaimsFail hs.params.ldt hs.params.shift θ (pcsMsg msgs hs 0).claims := by
  obtain ⟨proof, hact, hst1, hst2, hq, haccs, hlog, hshape, hvals, hcons, hzeta⟩ := hcheck
  have hrep : ∀ x : K, M.ext.toModel (rep M x) = x := fun x => Function.surjInv_eq M.surj x
  have heq : starkShape sys M.extData.d proof.active proof.logDegrees = v.shape M sys := by
    unfold ShardView.shape
    rw [hact, hlog]
  have key : ∀ (shape : ClaimShape)
      (htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F)),
      shape = v.shape M sys →
      ClaimsFail (modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)).ldt
        (modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)).shift θ
        ((modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)).claims
          (view M.toFieldModel sys.fri shape
            (firstMessage (v.commitments sys) (shapePoints (F := F) shape (rep M v.ζ))
              (valuesOf msgs)))
          (M.baseRows (comOf sys v msgs))) →
      ClaimsFail hs.params.ldt hs.params.shift θ (pcsMsg msgs hs 0).claims := by
    intro shape htwo h
    subst h
    exact id
  have hZF' : ZetaFail M sys θ (M.baseRows (comOf sys v msgs)) proof.active proof.logDegrees
      proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel (rep M v.β))
      (M.ext.toModel (rep M v.γ)) (M.ext.toModel v.acc0)
      (proof.intermediateAccumulators.map M.ext.toModel) (M.ext.toModel (rep M v.α))
      (M.ext.toModel (rep M v.ζ)) := by
    rw [hact, hlog, hst1, hst2, hq, haccs]
    simp only [hrep]
    exact hZF
  have hcf := claimsFail_of_zetaFail hfixed proof hshape (rep M v.β) (rep M v.γ) v.acc0
    (rep M v.α) (rep M v.ζ) hcons hzeta (by rw [heq]; exact hs.two)
    (by rw [heq]; exact hs.final) (by rw [heq]; exact hs.margin) hZF'
  rw [map_commitment_openingClaims v proof _ hst1 hst2 hq,
    claimPoints_openingClaims sys proof hshape, ← M.degree_eq, hvals] at hcf
  exact key _ (by rw [heq]; exact hs.two) heq hcf

/-- **An accepted transcript that is doomed has no failing constraint.** In a
doomed transcript that holds every round of the opening protocol of its shard,
if the executable checks pass on the opened values, the proof-of-work checks
pass and the opening protocol accepts, then no constraint of the shard fails on
any row, for the polynomials the committed columns decode to. -/
theorem good_of_sdoomedL (hfixed : sys.FixedOk) (hd : sdoomedL M sys V θ B msgs chals)
    {pre : BatchPreamble F D} (hdec : V.dec0 (rawAt msgs 0) = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D} (hhdr : pre.headers[V.shard (rawAt msgs 2)]? = some hdr)
    (hs : Supported M sys θ (viewOf M msgs chals hdr))
    (hlen : msgs.length = 4 + (hs.params.rounds + 2))
    (hcheck : (viewOf M msgs chals hdr).Check M sys (valuesOf msgs))
    (hpow : PowPasses (pcsT msgs chals hs (hs.params.rounds + 2)))
    (hacc : Accepts hs.params.ldt hs.params.shift
      (ungrind (pcsT msgs chals hs (hs.params.rounds + 2)))) :
    ¬ (viewOf M msgs chals hdr).CFail M sys θ
      (M.baseRows (comOf sys (viewOf M msgs chals hdr) msgs)) := by
  intro hCF
  obtain ⟨hZF, hP⟩ := ((hd pre hdec hpre).2 (by omega) hdr hhdr hs hCF).2 (by omega)
  have hgd := (pcsDoomed_iff (n := hs.params.rounds + 2) (by omega)).mp (hP (by omega) hcheck)
  have hfail : ClaimsFail hs.params.ldt hs.params.shift θ
      (claimsOf (ungrind (pcsT msgs chals hs (hs.params.rounds + 2)))) := by
    rw [claimsOf_ungrind_pcsT hs (hs.params.rounds + 1)]
    exact claimsFail_pcsMsg hfixed hs hcheck hZF
  exact not_grindDoomed_of_accepts _ hpow hfail hacc hgd

end State

end CertiFri.Exec.Stark
