import CertiFri.Params
import CertiFri.Claims
import CertiFri.Schedule

/-!
# The shape of a run

Everything about a run that is fixed before the proof is read: the distinct
heights of the folding inputs and the folding schedule. Both follow from the
parameters and the claims alone. Port of the first phase of `verify_fri` in
Plonky3 (`fri/src/verifier.rs`).

The heights are collected by insertion into a strictly decreasing list, so the
precondition of the schedule theorems holds by construction
(`distinctDesc_pairwise`), and the two schedule invariants transfer to the
derived shape (`deriveShape_sum`, `deriveShape_bounds`).

Not here yet: the parameter guards, the comparison of every proof-supplied
length against this shape, the transcript replay, the input openings, the fold
chains and the commitment checks.
-/

namespace CertiFri

/-- Insert `x` into a strictly decreasing list, dropping it if already present. -/
def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if y < x then x :: y :: ys
    else if y = x then y :: ys
    else y :: insertDesc x ys

/-- The distinct values of `heights`, largest first. -/
def distinctDesc (heights : List Nat) : List Nat :=
  heights.foldl (fun acc height => insertDesc height acc) []

theorem mem_insertDesc {x a : Nat} : ∀ {l : List Nat}, a ∈ insertDesc x l → a = x ∨ a ∈ l
  | [], h => by
    simp only [insertDesc, List.mem_singleton] at h
    exact Or.inl h
  | y :: ys, h => by
    unfold insertDesc at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self ..)
        · rcases mem_insertDesc h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem insertDesc_pairwise {x : Nat} :
    ∀ {l : List Nat}, l.Pairwise (· > ·) → (insertDesc x l).Pairwise (· > ·)
  | [], _ => by simp [insertDesc]
  | y :: ys, h => by
    have hy := (List.pairwise_cons.mp h).1
    have hys := (List.pairwise_cons.mp h).2
    unfold insertDesc
    split
    · next hlt =>
      refine List.pairwise_cons.mpr ⟨fun a ha => ?_, h⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hlt
      · have := hy a ha
        omega
    · split
      · exact h
      · next hnlt hne =>
        refine List.pairwise_cons.mpr ⟨fun a ha => ?_, insertDesc_pairwise hys⟩
        rcases mem_insertDesc ha with rfl | ha
        · omega
        · exact hy a ha

theorem distinctDesc_pairwise (heights : List Nat) : (distinctDesc heights).Pairwise (· > ·) := by
  suffices ∀ (heights acc : List Nat), acc.Pairwise (· > ·) →
      (heights.foldl (fun acc height => insertDesc height acc) acc).Pairwise (· > ·) from
    this heights [] List.Pairwise.nil
  intro heights
  induction heights with
  | nil => intro acc h; exact h
  | cons height heights ih => intro acc h; exact ih _ (insertDesc_pairwise h)

/-- What is fixed about a run before the proof is read. -/
structure Shape where
  /-- Distinct log-heights of the folding inputs, tallest first. -/
  inputLogHeights : List Nat
  /-- One log-arity per commit round, in round order. -/
  logArities : List Nat
  deriving Repr, DecidableEq

/-- Log-height of the evaluation domain folding starts from, or zero when
nothing is committed. -/
def Shape.logGlobalMaxHeight (shape : Shape) : Nat := shape.inputLogHeights.headD 0

/-- The log-height of the committed codeword of every claimed matrix. -/
def claimedLogHeights {EF Commitment : Type} (params : FriParams)
    (claims : Array (CommitmentOpening EF Commitment)) : List Nat :=
  claims.toList.flatMap fun claim =>
    claim.matrices.toList.map fun matrix => matrix.logDegree + params.logBlowup

/-- Derive the shape of a run from the parameters and the claims. -/
def deriveShape {EF Commitment : Type} (params : FriParams)
    (claims : Array (CommitmentOpening EF Commitment)) : Shape :=
  let inputLogHeights := distinctDesc (claimedLogHeights params claims)
  { inputLogHeights
    logArities := foldSchedule inputLogHeights params.logFinalHeight params.maxLogArity }

theorem deriveShape_pairwise {EF Commitment : Type} (params : FriParams)
    (claims : Array (CommitmentOpening EF Commitment)) :
    (deriveShape params claims).inputLogHeights.Pairwise (· > ·) :=
  distinctDesc_pairwise _

/-- The total reduction is the tallest claimed log-height minus the final
log-height, truncated at zero. Inputs already at or below the final height
produce no rounds. Requires a positive arity cap. -/
theorem deriveShape_sum {EF Commitment : Type} (params : FriParams)
    (claims : Array (CommitmentOpening EF Commitment)) (hcap : 0 < params.maxLogArity) :
    (deriveShape params claims).logArities.sum
      = (deriveShape params claims).logGlobalMaxHeight - params.logFinalHeight := by
  have hsorted := deriveShape_pairwise params claims
  simp only [deriveShape, Shape.logGlobalMaxHeight] at hsorted ⊢
  cases hheights : distinctDesc (claimedLogHeights params claims) with
  | nil => simp [foldSchedule]
  | cons tallest rest =>
    rw [hheights] at hsorted
    simpa using foldSchedule_sum hsorted hcap

/-- Every round of the derived schedule folds by at least one bit and at most
the configured cap. -/
theorem deriveShape_bounds {EF Commitment : Type} (params : FriParams)
    (claims : Array (CommitmentOpening EF Commitment)) (hcap : 0 < params.maxLogArity) :
    ∀ a ∈ (deriveShape params claims).logArities, 1 ≤ a ∧ a ≤ params.maxLogArity := by
  have hsorted := deriveShape_pairwise params claims
  simp only [deriveShape] at hsorted ⊢
  cases hheights : distinctDesc (claimedLogHeights params claims) with
  | nil => simp [foldSchedule]
  | cons tallest rest =>
    rw [hheights] at hsorted
    exact foldSchedule_bounds hsorted hcap

end CertiFri
