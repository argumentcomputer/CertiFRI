import CertiFriProofs.Exec.Stark.Link
import CertiFriProofs.Exec.Stark.Free
import CertiFriProofs.Theory.Oracle.MerkleCommitted

/-!
# The messages of the STARK, as the security proof reads them

Definitions shared by the state function of the STARK (`Exec/Stark/State.lean`)
and the theorems about it.

## Contents

* `Bounds`: bounds on the sizes of what a prover sends. `HeaderOk`, `PreOk`: a
  header and a preamble within the bounds.
* `IMsg`, `digestsOf`, `readMsg`: a message is what the verifier absorbed
  together with the rows its commitments open to.
* `Variant`: how an entry point of the verifier lays out its transcript.
* `rawAt`, `comAt`, `ansAt`, `fieldAt`: the messages and the challenges of a
  transcript, by round. `extsOf`: the extension-field elements of a message.
* `shapePoints`, `claimPoints_openingClaims`: the opening points of a shape.
* `headerItems`, `allItems`: the lookup messages of a shard and of a preamble,
  read off the polynomials the committed columns decode to. `itemBound`,
  `lenBound`, `length_allItems_le`, `length_args_allItems_le`: their number and
  their lengths, for a preamble within the bounds.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D]

/-! ## Messages -/

/-- Bounds on the sizes of what a prover sends: the number of shards, the
number of public claims of a shard, the number of messages of a batch, and the
length of a claim or of a message. -/
structure Bounds where
  /-- The number of shards. -/
  shards : ℕ
  /-- The number of public claims of a shard. -/
  claims : ℕ
  /-- The number of messages of a batch. -/
  messages : ℕ
  /-- The length of a claim or of a message. -/
  len : ℕ

/-- A message, as the state function reads it: what the verifier absorbed, and
the rows its commitments open to. -/
abbrev IMsg (F EF D K : Type) : Type := RawMsg F EF D × Compiled.Committed K D

/-- The commitments of a raw message that are read: its first digests, one more
than the number of shards. -/
def digestsOf (B : Bounds) (m : RawMsg F EF D) : List D :=
  (digestsIn m).take (B.shards + 1)

/-- A raw message with the committed rows of its commitments. -/
def readMsg (B : Bounds) (m : RawMsg F EF D) (c : Compiled.Committed K D) : IMsg F EF D K :=
  (m, fun root => if root ∈ digestsOf B m then c root else fun _ _ _ => none)

/-- How an entry point of the verifier lays out its transcript: the preamble
its first message encodes, and the position of the shard a chain is about, read
off the message of round `2`. -/
structure Variant (F EF D : Type) where
  /-- The preamble a first message encodes, if it encodes one. -/
  dec0 : RawMsg F EF D → Option (BatchPreamble F D)
  /-- The position of the shard, read off the message of round `2`. -/
  shard : RawMsg F EF D → ℕ

/-- A header within the size bounds, for a system. -/
structure HeaderOk (sys : System F D) (B : Bounds) (h : ShardHeader F D) : Prop where
  /-- One activation bit per circuit. -/
  active : h.active.size = sys.circuits.size
  /-- One trace height per active circuit. -/
  logDegrees : h.logDegrees.size = (activeIndices h.active).length
  /-- The trace heights are supported. -/
  logDegree_le : ∀ pos, h.logDegrees.getD pos 0 ≤ sys.maxLogDegree
  /-- The number of public claims. -/
  claims : h.claims.size ≤ B.claims
  /-- The length of a public claim. -/
  claim_len : ∀ c ∈ h.claims, c.size ≤ B.len

/-- A preamble within the size bounds, for a system. -/
structure PreOk (sys : System F D) (B : Bounds) (pre : BatchPreamble F D) : Prop where
  /-- The number of shards. -/
  shards : pre.headers.size ≤ B.shards
  /-- Every header is within the bounds. -/
  header : ∀ h ∈ pre.headers, HeaderOk sys B h
  /-- The number of messages. -/
  messages : pre.messages.size ≤ B.messages
  /-- The length of a message. -/
  message_len : ∀ m ∈ pre.messages, m.args.size ≤ B.len

/-! ## Reading a transcript -/

section Read

variable {slots width : ℕ} (msgs : List (IMsg F EF D K)) (chals : List (UAns K slots width))

/-- What the verifier absorbed in round `j`; nothing if there is no such
round. -/
def rawAt (j : ℕ) : RawMsg F EF D := (msgs[j]?.map Prod.fst).getD []

/-- The committed rows of the message of round `j`. -/
def comAt (j : ℕ) : Compiled.Committed K D :=
  (msgs[j]?.map Prod.snd).getD fun _ _ _ _ => none

/-- The answer of round `j`. -/
def ansAt (j : ℕ) : UAns K slots width :=
  chals[j]?.getD (0, fun _ => ⟨0, Nat.two_pow_pos _⟩)

/-- The field challenge of round `j`. -/
def fieldAt (j : ℕ) : K := (ansAt chals j).field

end Read

/-- The extension-field elements of a raw message, in order. -/
def extsOf (m : RawMsg F EF D) : List EF :=
  m.filterMap fun
    | .ext e => some e
    | _ => none

/-- The opening points of a shape at `ζ`: the first point of a matrix is `ζ`,
a second one its successor on the trace domain of the matrix. -/
def shapePoints (shape : ClaimShape) (ζ : EF) : Array EF :=
  (shape.flatMap fun mats => mats.flatMap fun m =>
    (List.range m.numPoints).map fun p =>
      if p = 0 then ζ else nextPoint (F := F) m.logDegree ζ).toArray

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- What the shape check says about the numbers of opened rows: the bitmap has
one bit per circuit, the fixed trace of an inactive circuit is opened on one
row, and for an active circuit the main trace and the lookup trace are opened
on two rows, the quotient on one and the fixed trace on two. -/
private theorem shapeOk_rows {InputProof CommitProof : Type} {sys : System F D}
    {proof : Proof F EF D InputProof CommitProof} (h : shapeOk sys proof = true) :
    proof.active.size = sys.circuits.size ∧
    (∀ ci < sys.circuits.size, proof.active.getD ci false = false →
      (sys.preprocessedIndices.getD ci none).isNone = false →
      (preprocessedRows sys proof ci).size = 1) ∧
    ∀ p ∈ (activeIndices proof.active).zipIdx,
      (proof.stage1Opened.getD p.2 #[]).size = 2 ∧ (proof.stage2Opened.getD p.2 #[]).size = 2 ∧
      (proof.quotientOpened.getD p.2 #[]).size = 1 ∧
      ((sys.preprocessedIndices.getD p.1 none).isNone = false →
        (preprocessedRows sys proof p.1).size = 2) := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, rowsOk, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hin⟩, hact⟩ := h
  refine ⟨hsize, fun ci hci ha hp => ?_, fun p hp => ?_⟩
  · rcases hin ci hci with (ha' | hp') | h1
    · rw [ha] at ha'
      exact absurd ha' (by simp)
    · rw [hp] at hp'
      exact absurd hp' (by simp)
    · exact h1.1
  · obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩ := hact p hp
    refine ⟨h1.1, h2.1, h4.1, fun hpre => ?_⟩
    rcases h3 with h3 | h3
    · rw [hpre] at h3
      exact absurd h3 (by simp)
    · exact h3.1

omit [FieldOps EF] in
/-- The opening points of a matrix opened at as many points as it has rows. -/
private theorem points_matrixOpening (k : ℕ) (points : List EF) (rows : Array (Array EF))
    (h : points.length = rows.size) :
    (matrixOpening k points rows).points.toList.map (·.point) = points := by
  simp only [matrixOpening, List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_fst_zip (by simp [h]))

/-- The opening points of the traces of the active circuits, each opened on
`n` rows, are those of their shapes. -/
private theorem points_traces (act : List ℕ) (logDegrees : Array ℕ) (width : ℕ → ℕ) (n : ℕ)
    (ζ : EF) (opened : Array (Array (Array EF)))
    (h : ∀ p ∈ act.zipIdx, (opened.getD p.2 #[]).size = n) :
    ((act.zipIdx.map fun (_, pos) =>
        matrixOpening (logDegrees.getD pos 0)
          ((List.range n).map fun p =>
            if p = 0 then ζ else nextPoint (F := F) (logDegrees.getD pos 0) ζ)
          (opened.getD pos #[])).flatMap fun m => m.points.toList.map (·.point)) =
      (traceShapes act logDegrees width n).flatMap fun m =>
        (List.range m.numPoints).map fun p =>
          if p = 0 then ζ else nextPoint (F := F) m.logDegree ζ := by
  rw [traceShapes, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  exact points_matrixOpening _ _ _ (by rw [List.length_map, List.length_range, h p hp])

omit [Inhabited D] [DecidableEq D] in
/-- The opening points of the fixed traces of a proof that passes the shape
check are those of their shapes. -/
private theorem points_fixed {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (h : shapeOk sys proof = true) (ζ : EF) :
    (((List.range sys.circuits.size).filterMap fun ci =>
      if (sys.preprocessedIndices.getD ci none).isNone then none
      else
        match (activeIndices proof.active).idxOf? ci with
        | some pos =>
          some (matrixOpening (proof.logDegrees.getD pos 0)
            [ζ, nextPoint (F := F) (proof.logDegrees.getD pos 0) ζ]
            (preprocessedRows sys proof ci))
        | none =>
          some (matrixOpening (Nat.log2 (sys.circuits.getD ci default).preprocessedHeight)
            [ζ] (preprocessedRows sys proof ci))).flatMap fun m =>
        m.points.toList.map (·.point)) =
      (fixedShapes sys (activeIndices proof.active) proof.logDegrees).flatMap fun m =>
        (List.range m.numPoints).map fun p =>
          if p = 0 then ζ else nextPoint (F := F) m.logDegree ζ := by
  obtain ⟨hsize, hin, hact⟩ := shapeOk_rows h
  rw [fixedShapes, List.flatMap_def, List.flatMap_def, List.map_filterMap, List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun ci hci => ?_
  by_cases hpre : (sys.preprocessedIndices.getD ci none).isNone = true
  · rw [ite_eq_left hpre, ite_eq_left hpre]
    rfl
  · rw [ite_eq_right hpre, ite_eq_right hpre]
    rw [Bool.not_eq_true] at hpre
    cases hidx : (activeIndices proof.active).idxOf? ci with
    | none =>
      have hmem : ci ∉ activeIndices proof.active := List.idxOf?_eq_none_iff.mp hidx
      have ha : proof.active.getD ci false = false := by
        by_contra hne
        exact hmem (List.mem_filter.mpr ⟨by rw [hsize]; exact hci, by simpa using hne⟩)
      have hrows := hin ci (List.mem_range.mp hci) ha hpre
      simp only [Option.map_some]
      rw [points_matrixOpening _ _ _ (by rw [hrows]; rfl)]
      rfl
    | some pos =>
      have hmem : (ci, pos) ∈ (activeIndices proof.active).zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?]
        obtain ⟨hlt, heq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
        rw [List.getElem?_eq_getElem hlt]
        exact congrArg some (by simpa using heq)
      have hrows := (hact _ hmem).2.2.2 hpre
      simp only [Option.map_some]
      rw [points_matrixOpening _ _ _ (by rw [hrows]; rfl)]
      rfl

omit [Inhabited D] [DecidableEq D] in
/-- The opening points of a proof that passes the shape check are those of its
shape. -/
theorem claimPoints_openingClaims {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (h : shapeOk sys proof = true) (ζ : EF) :
    claimPoints (openingClaims sys proof ζ) =
      shapePoints (F := F) (starkShape sys (ExtensionOps.degree (F := F) (EF := EF)) proof.active
        proof.logDegrees) ζ := by
  obtain ⟨-, -, hact⟩ := shapeOk_rows h
  have h1 := points_traces (F := F) (activeIndices proof.active) proof.logDegrees
    (fun ci => (sys.circuits.getD ci default).mainWidth) 2 ζ proof.stage1Opened
    fun p hp => (hact p hp).1
  have h2 := points_traces (F := F) (activeIndices proof.active) proof.logDegrees
    (fun ci => (sys.circuits.getD ci default).stage2Width) 2 ζ proof.stage2Opened
    fun p hp => (hact p hp).2.1
  have h3 := points_traces (F := F) (activeIndices proof.active) proof.logDegrees
    (fun ci => (sys.circuits.getD ci default).quotientDegree *
      ExtensionOps.degree (F := F) (EF := EF)) 1 ζ proof.quotientOpened
    fun p hp => (hact p hp).2.2.1
  have h4 := points_fixed sys proof h ζ
  rw [claimPoints, shapePoints, openingClaims, starkShape]
  congr 1
  cases sys.preprocessedCommit with
  | none =>
    simp only [Array.toList_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    rw [← h1, ← h2, ← h3]
    rfl
  | some c =>
    simp only [Array.toList_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    rw [← h1, ← h2, ← h3, ← h4]
    rfl

/-! ## The lookup messages of a preamble -/

section Items

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (com : Compiled.Committed K D)

/-- The lookup messages of one shard: its public claims, each with multiplicity
one, and what its active circuits send on the rows of their traces, read off
the polynomials the committed columns decode to. -/
noncomputable def headerItems (h : ShardHeader F D) : List (K × List K) :=
  (h.claims.toList.map fun c => ((1 : K), c.toList.map M.base.toModel)) ++
    (activeIndices h.active).zipIdx.flatMap fun p =>
      circuitItems M.base.toModel (sys.circuits.getD p.1 default)
        (fun r => pointRow (sys.circuits.getD p.1 default) (2 ^ h.logDegrees.getD p.2 0)
          (M.gen (h.logDegrees.getD p.2 0))
          (shardCols M sys θ com h.active h.logDegrees h.stage1Commit default default p.2 p.1)
          #[] (M.gen (h.logDegrees.getD p.2 0) ^ r))
        (2 ^ h.logDegrees.getD p.2 0)

/-- The lookup messages of a preamble: those of every shard, and the messages
of the batch with their multiplicities. -/
noncomputable def allItems (pre : BatchPreamble F D) : List (K × List K) :=
  pre.headers.toList.flatMap (headerItems M sys θ com) ++
    pre.messages.toList.map fun m =>
      (M.base.toModel m.multiplicity, m.args.toList.map M.base.toModel)

/-- A bound on the number of lookup messages of a preamble within the size
bounds. -/
def itemBound (sys : System F D) (B : Bounds) : ℕ :=
  B.shards * (B.claims +
    (sys.circuits.toList.map fun c => 2 ^ sys.maxLogDegree * c.graph.lookups.size).sum)
    + B.messages

/-- A bound on the length of a lookup message. -/
def lenBound (sys : System F D) (B : Bounds) : ℕ :=
  max B.len ((sys.circuits.toList.map fun c =>
    (c.graph.lookups.toList.map fun l => l.args.size).foldr max 0).foldr max 0)

variable {M sys θ com}

omit [FieldOps F] [TwoAdicOps F] [DecidableEq K] in
/-- The number of messages a circuit sends on `n` rows: one per row and
lookup. -/
private theorem length_circuitItems (ι : F → K) (c : Circuit F) (rows : ℕ → RowValues K)
    (n : ℕ) : (circuitItems ι c rows n).length = n * c.graph.lookups.size := by
  simp [circuitItems, List.length_flatMap]

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- The circuits of a system, read by position. -/
private theorem toList_circuits :
    sys.circuits.toList =
      (List.range sys.circuits.size).map fun ci => sys.circuits.getD ci default := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp at h₁
  simp [h₁]

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- An active circuit of a bitmap with one bit per circuit is a circuit of the
system. -/
private theorem getD_mem_circuits {active : Array Bool}
    (hsize : active.size = sys.circuits.size) {p : ℕ × ℕ}
    (hp : p ∈ (activeIndices active).zipIdx) :
    sys.circuits.getD p.1 default ∈ sys.circuits.toList := by
  have hmem : p.1 ∈ activeIndices active :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have hlt : p.1 < sys.circuits.size := by
    rw [← hsize]
    exact List.mem_range.mp (List.mem_filter.mp hmem).1
  rw [toList_circuits]
  exact List.mem_map.mpr ⟨p.1, List.mem_range.mpr hlt, rfl⟩

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- A sum over the active circuits of a bitmap with one bit per circuit is at
most the sum over all circuits. -/
private theorem sum_activeIndices_le {active : Array Bool}
    (hsize : active.size = sys.circuits.size) (f : Circuit F → ℕ) :
    ((activeIndices active).map fun ci => f (sys.circuits.getD ci default)).sum ≤
      (sys.circuits.toList.map f).sum := by
  rw [toList_circuits, List.map_map, ← hsize]
  exact List.Sublist.sum_le_sum (List.Sublist.map _ List.filter_sublist) fun _ _ => Nat.zero_le _

/-- An element of a list of numbers is at most their maximum. -/
private theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

omit [DecidableEq D] in
/-- A header within the size bounds has at most as many lookup messages as the
bound on its claims and, for every circuit of the system, one per lookup and
row of the tallest trace. -/
private theorem length_headerItems_le {B : Bounds} {h : ShardHeader F D}
    (hh : HeaderOk sys B h) :
    (headerItems M sys θ com h).length ≤ B.claims +
      (sys.circuits.toList.map fun c => 2 ^ sys.maxLogDegree * c.graph.lookups.size).sum := by
  rw [headerItems, List.length_append, List.length_flatMap, List.length_map,
    Array.length_toList (xs := h.claims)]
  refine Nat.add_le_add hh.claims ?_
  calc _ ≤ ((activeIndices h.active).zipIdx.map fun p =>
        2 ^ sys.maxLogDegree * (sys.circuits.getD p.1 default).graph.lookups.size).sum :=
        List.sum_le_sum fun p _ => by
          rw [length_circuitItems]
          exact Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by norm_num) (hh.logDegree_le _))
    _ = ((activeIndices h.active).map fun ci =>
        2 ^ sys.maxLogDegree * (sys.circuits.getD ci default).graph.lookups.size).sum := by
        conv_rhs => rw [← List.zipIdx_map_fst 0 (activeIndices h.active), List.map_map]
        rfl
    _ ≤ _ := sum_activeIndices_le hh.active fun c =>
        2 ^ sys.maxLogDegree * c.graph.lookups.size

omit [DecidableEq D] in
/-- A preamble within the size bounds has at most `itemBound` lookup
messages. -/
theorem length_allItems_le {B : Bounds} {pre : BatchPreamble F D} (hpre : PreOk sys B pre) :
    (allItems M sys θ com pre).length ≤ itemBound sys B := by
  rw [allItems, List.length_append, List.length_flatMap, List.length_map,
    Array.length_toList (xs := pre.messages), itemBound]
  refine Nat.add_le_add (le_trans (List.sum_le_length_nsmul _ (B.claims +
    (sys.circuits.toList.map fun c => 2 ^ sys.maxLogDegree * c.graph.lookups.size).sum)
    fun x hx => ?_) ?_) hpre.messages
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    exact length_headerItems_le (hpre.header h (Array.mem_toList_iff.mp hh))
  · rw [List.length_map, Array.length_toList, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hpre.shards

omit [DecidableEq D] in
/-- The lookup messages of a preamble within the size bounds have length at
most `lenBound`. -/
theorem length_args_allItems_le {B : Bounds} {pre : BatchPreamble F D} (hpre : PreOk sys B pre) :
    ∀ it ∈ allItems M sys θ com pre, it.2.length ≤ lenBound sys B := by
  intro it hit
  rw [allItems, List.mem_append] at hit
  rcases hit with hit | hit
  · obtain ⟨h, hh, hit⟩ := List.mem_flatMap.mp hit
    have hok := hpre.header h (Array.mem_toList_iff.mp hh)
    rw [headerItems, List.mem_append] at hit
    rcases hit with hit | hit
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hit
      rw [List.length_map, Array.length_toList]
      exact (hok.claim_len c (Array.mem_toList_iff.mp hc)).trans (le_max_left _ _)
    · obtain ⟨p, hp, hit⟩ := List.mem_flatMap.mp hit
      rw [circuitItems] at hit
      obtain ⟨r, -, hit⟩ := List.mem_flatMap.mp hit
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hit
      rw [List.length_map, Array.length_toList]
      exact le_trans
        (le_trans (le_foldr_max (List.mem_map_of_mem (f := fun l => l.args.size) hl))
          (le_foldr_max (List.mem_map_of_mem
            (f := fun c : Circuit F =>
              (c.graph.lookups.toList.map fun l => l.args.size).foldr max 0)
            (getD_mem_circuits hok.active hp))))
        (le_max_right _ _)
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hit
    rw [List.length_map, Array.length_toList]
    exact (hpre.message_len m (Array.mem_toList_iff.mp hm)).trans (le_max_left _ _)

end Items

end CertiFri.Exec.Stark
