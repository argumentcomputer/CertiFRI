import CertiFriProofs.Theory.Compiled.Tensor
import CertiFriProofs.Theory.MultiArity.PcsRbrTensor
import CertiFriProofs.Theory.Oracle.SpongeCommitted

/-!
# Compiled multi-arity tensor-batched FRI verifier, chained-ROM & sponge soundness

Generalizes `Theory/Compiled/{Read,Verifier,Accepts,Tensor,AcceptsComTensor}.lean`
and `Sponge/SpongeChalTensor` (`Exec/SoundnessTensorSponge.lean`) to variable
per-round folding schedules `arities : List ℕ` (covering `a ∈ {1, 2, 3}`, fold
factors `2, 4, 8`).

## Contents

1. `MultiParams F` & `MultiProof F D batches queries`:
   public parameters with per-round log-arity schedule `arities`, round-level
   claims at cumulative log-arities `cum j = Fri.cumLogArity arities j`,
   commit-phase matrix dimensions `#[⟨2 ^ logArity i, n - cum (i + 1)⟩]`, and
   `2 ^ logArity i - 1` sibling values per round per query.
2. `MultiParams.read`, `MultiParams.verifyWithTensor`, `queryBound_verifyWithTensor`,
   `run_verifyWithTensor`, `verifyGrindViewTensor`.
3. `MultiParams.acceptsTensorMulti_of_outcome_verifyWithTensor_view` and
   `MultiParams.acceptsTensorMulti_of_outcome_verifyWithTensor_view_com` (for
   claims read from base-field committed rows `c`, matching `AcceptsComTensor.lean`).
4. `MultiParams.soundness_grind_view_tensorMulti_of_imp`: chained-ROM soundness.
5. `SpongeChalTensorMulti`, `rbrSound_spongeTensorMulti`: single-root incremental
   sponge lift (`entryCap = 1`, classical BCS collision prefactor `c = 3 / 2`).
-/

namespace CertiFri.Compiled

open Polynomial Oracle OracleComp MerkleRO
open PcsRbr (TensorChal tensorCoordWeight reducedOpeningTensor pcsInputTensor
  ChalTensorMulti tensorOfMulti betasOfTensorMulti queriesOfTensorMulti claimsOf wordsOf
  ClaimsFailMulti AcceptsTensorMulti GrindChal PowPasses ungrind roundErrorTensor)

/-! ## 1. Multi-arity compiled parameters and reading -/

/-- Public parameters of the compiled multi-arity FRI protocol, with per-round
log-arity schedule `arities : List ℕ`. Round `i < arities.length` folds by
factor `2 ^ (arities.getD i 0)` from level `cumLogArity arities i` to level
`cumLogArity arities (i + 1)`. -/
structure MultiParams (F : Type) [Field F] where
  ω : F
  n : ℕ
  arities : List ℕ
  finalDegree : ℕ
  shift : F
  queries : ℕ
  batches : ℕ
  dims : Fin batches → Array Dimensions
  numClaims : ℕ → ℕ
  slot : ∀ j, Fin (numClaims j) → Slot batches
  prim : IsPrimitiveRoot ω (2 ^ n)
  arities_pos : ∀ a ∈ arities, 0 < a
  arities_sum_le : arities.sum ≤ n
  shift_ne : shift ≠ 0
  height_le : ∀ b, Merkle.maxLogHeight (dims b).toList ≤ n
  slot_dims : ∀ j ≤ arities.length, ∀ k : Fin (numClaims j), ∃ d : Dimensions,
    (dims (slot j k).batch)[(slot j k).matrix]? = some d ∧
      d.logHeight = n - Fri.cumLogArity arities j ∧
      (slot j k).col < d.width

/-- Multi-arity proof data: same as `Compiled.Proof` except each folding round
carries an array of `2 ^ a - 1` sibling values per query. -/
structure MultiProof (F D : Type) (batches queries : ℕ) where
  inputRows : Fin batches → Fin queries → Array (Array F)
  inputPaths : Fin batches → Fin queries → List D
  siblings : ℕ → Fin queries → Array F
  commitPaths : ℕ → Fin queries → List D

/-- Model-field `placeRowMulti`: reconstruct the `arity`-entry row from the
current folded value at `idxInGroup` and the `arity - 1` sibling values. -/
def placeRowMultiM {F : Type} [Field F] (arity : ℕ) (folded : F) (siblings : Array F)
    (idxInGroup : ℕ) : Array F :=
  Array.ofFn (n := arity) fun j =>
    if j.val = idxInGroup then folded
    else if j.val < idxInGroup then siblings.getD j.val 0
    else siblings.getD (j.val - 1) 0

theorem placeRowMultiM_self {F : Type} [Field F] {arity idxInGroup : ℕ} (hidx : idxInGroup < arity)
    (folded : F) (siblings : Array F) :
    (placeRowMultiM arity folded siblings idxInGroup).getD idxInGroup 0 = folded := by
  rw [placeRowMultiM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hidx,
    Option.getD_some, ite_eq_left rfl]

namespace MultiParams

variable {F D : Type} [Field F] (P : MultiParams F)

/-- Number of folding rounds (`P.arities.length`). -/
abbrev rounds : ℕ := P.arities.length

/-- Cumulative log-arity folded before round `j`. -/
abbrev cum (j : ℕ) : ℕ := Fri.cumLogArity P.arities j

/-- Log-arity of folding round `i` (`0` past `P.rounds`). -/
abbrev logArity (i : ℕ) : ℕ := P.arities.getD i 0

theorem rounds_le : P.rounds ≤ P.n := by
  have hlen : P.arities.length ≤ P.arities.sum := by
    have haux : ∀ l : List ℕ, (∀ a ∈ l, 0 < a) → l.length ≤ l.sum := fun l hl => by
      induction l with
      | nil => simp
      | cons a as ih =>
        have ha := hl a List.mem_cons_self
        have has := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
        simp only [List.length_cons, List.sum_cons]
        omega
    exact haux P.arities P.arities_pos
  exact hlen.trans P.arities_sum_le

theorem cum_le_n (j : ℕ) : P.cum j ≤ P.n :=
  (Fri.cumLogArity_le_sum P.arities j).trans P.arities_sum_le

theorem cum_succ {i : ℕ} (hi : i < P.rounds) :
    P.cum (i + 1) = P.cum i + P.logArity i := by
  unfold cum logArity
  rw [Fri.cumLogArity_succ P.arities hi, List.getD_eq_getElem _ _ hi]

theorem logArity_pos {i : ℕ} (hi : i < P.rounds) : 0 < P.logArity i := by
  unfold logArity
  rw [List.getD_eq_getElem _ _ hi]
  exact P.arities_pos _ (List.getElem_mem hi)

/-- The multi-arity low-degree test instance on the two-adic domains of `P.ω`. -/
def ldt [DecidableEq F] : MultiLdtInstance F :=
  twoAdicMultiInstance P.ω P.n P.arities P.finalDegree P.prim P.arities_pos P.arities_sum_le

@[simp] theorem ldt_rounds [DecidableEq F] : P.ldt.rounds = P.rounds := rfl
@[simp] theorem ldt_logArity [DecidableEq F] (i : ℕ) : P.ldt.logArity i = P.logArity i := rfl
@[simp] theorem ldt_domain [DecidableEq F] (i : ℕ) :
    P.ldt.domain i = twoAdicDomain P.ω P.n (P.cum i) := rfl
@[simp] theorem ldt_degree [DecidableEq F] (i : ℕ) :
    P.ldt.degree i = 2 ^ (P.arities.sum - P.cum i) * P.finalDegree := rfl
@[simp] theorem ldt_zeta [DecidableEq F] (i : ℕ) :
    P.ldt.zeta i = P.ω ^ 2 ^ (P.n - P.logArity i) := rfl

theorem ldt_cumLog [DecidableEq F] {i : ℕ} (hi : i ≤ P.rounds) :
    P.ldt.cumLog i = P.cum i :=
  cumLog_twoAdicMultiInstance P.ω P.n P.arities P.finalDegree P.prim P.arities_pos
    P.arities_sum_le i hi

theorem domain_zero_nonempty [DecidableEq F] : (P.ldt.domain 0).Nonempty :=
  ⟨_, pointOfIndex_mem_twoAdicDomain' P.prim (Nat.zero_le _) 0⟩

/-- Dimensions of round `i`'s committed codeword matrix: width `2 ^ logArity i`,
log-height `n - cum (i + 1)`. -/
def commitDims (i : ℕ) : Array Dimensions :=
  #[⟨2 ^ P.logArity i, P.n - P.cum (i + 1)⟩]

/-- Query bound of the compiled multi-arity verifier. -/
def verifierQueries : ℕ :=
  (P.batches + P.rounds) * (P.queries * (3 * P.n + 1))

/-! ## Reading messages against committed rows -/

section Read

variable [DecidableEq F]

/-- Claims of round-level `j`, read from committed rows at domain `twoAdicDomain ω n (cum j)`. -/
def claims (msg : Msg F D P.batches) (committed : Committed F D) (j : ℕ)
    (k : Fin (P.numClaims j)) : Claim F where
  f := ofIndexed (2 ^ (P.n - P.cum j))
    (fun i => P.shift * pointOfIndex P.ω P.n (P.n - P.cum j) i) fun i =>
      entry (committed (msg.inputRoots (P.slot j k).batch) (P.dims (P.slot j k).batch)
        (P.slot j k).matrix i) (P.slot j k).col
  z := msg.point j k
  y := msg.value j k

/-- Word of folding round `i`, read from its `width = 2 ^ logArity i` commitment:
at `pointOfIndex ω n (n - cum i) idx`, it reads entry `idx % 2 ^ a` of row `idx / 2 ^ a`. -/
def commitWord (i : ℕ) (rows : ℕ → Option (Array F)) : F → F :=
  ofIndexed (2 ^ (P.n - P.cum i)) (pointOfIndex P.ω P.n (P.n - P.cum i)) fun idx =>
    entry (rows (idx / 2 ^ P.logArity i)) (idx % 2 ^ P.logArity i)

/-- Final word: evaluation of the polynomial given by the first `finalDegree` coefficients. -/
noncomputable def finalWord (coeffs : List F) (x : F) : F :=
  (polyOfCoeffs (coeffs.take P.finalDegree)).eval x

/-- Read round `j`'s message against `committed`. -/
noncomputable def read (j : ℕ) (msg : Msg F D P.batches) (committed : Committed F D) :
    PcsRbr.Msg F P.numClaims where
  claims := if j = 0 then P.claims msg committed else fun _ _ => ⟨fun _ => 0, 0, 0⟩
  word :=
    if j = 0 then fun _ => 0
    else if j ≤ P.rounds then
      P.commitWord (j - 1) (committed msg.commitRoot (P.commitDims (j - 1)) 0)
    else P.finalWord msg.finalCoeffs

@[simp] theorem read_claims_zero (msg : Msg F D P.batches) (committed : Committed F D) :
    (P.read 0 msg committed).claims = P.claims msg committed := rfl

theorem read_word_of_lt {i : ℕ} (hi : i < P.rounds) (msg : Msg F D P.batches)
    (committed : Committed F D) :
    (P.read (i + 1) msg committed).word =
      P.commitWord i (committed msg.commitRoot (P.commitDims i) 0) := by
  simp only [read, Nat.succ_ne_zero, ↓reduceIte, ite_eq_left (Nat.succ_le_of_lt hi),
    Nat.add_sub_cancel]

theorem read_word_last (msg : Msg F D P.batches) (committed : Committed F D) :
    (P.read (P.rounds + 1) msg committed).word = P.finalWord msg.finalCoeffs := by
  simp only [read, Nat.succ_ne_zero, ↓reduceIte, ite_eq_right (Nat.not_succ_le_self _)]

theorem read_congr (j : ℕ) (msg : Msg F D P.batches) (c c' : Committed F D)
    (h : ∀ root ∈ digestsOfAt P.rounds j msg, c root = c' root) :
    P.read j msg c = P.read j msg c' := by
  by_cases hj0 : j = 0
  · subst hj0
    have hin : ∀ b, c (msg.inputRoots b) = c' (msg.inputRoots b) := fun b =>
      h _ (inputRoots_mem_digestsOfAt P.rounds msg b)
    have hclaims : P.claims msg c = P.claims msg c' := by
      funext l k; simp only [claims, hin]
    simp only [read, ↓reduceIte, hclaims]
  · by_cases hjr : j ≤ P.rounds
    · have hcommit : c msg.commitRoot = c' msg.commitRoot :=
        h _ (commitRoot_mem_digestsOfAt hj0 hjr msg)
      simp only [read, hj0, ↓reduceIte, hjr, hcommit]
    · simp only [read, hj0, ↓reduceIte, hjr]

theorem claims_f_apply (msg : Msg F D P.batches) (committed : Committed F D) {j : ℕ}
    (k : Fin (P.numClaims j)) {i : ℕ} (hi : i < 2 ^ (P.n - P.cum j)) :
    (P.claims msg committed j k).f (P.shift * pointOfIndex P.ω P.n (P.n - P.cum j) i) =
      entry (committed (msg.inputRoots (P.slot j k).batch) (P.dims (P.slot j k).batch)
        (P.slot j k).matrix i) (P.slot j k).col :=
  ofIndexed_apply (g := fun i => P.shift * pointOfIndex P.ω P.n (P.n - P.cum j) i)
    (fun _ ha _ hb hab =>
      (pointOfIndex_inj P.prim (Nat.sub_le _ _) ha hb).mp (mul_left_cancel₀ P.shift_ne hab))
    (fun i => entry (committed (msg.inputRoots (P.slot j k).batch) (P.dims (P.slot j k).batch)
      (P.slot j k).matrix i) (P.slot j k).col) hi

theorem commitWord_apply (i : ℕ) (rows : ℕ → Option (Array F)) {idx : ℕ}
    (hidx : idx < 2 ^ (P.n - P.cum i)) :
    P.commitWord i rows (pointOfIndex P.ω P.n (P.n - P.cum i) idx) =
      entry (rows (idx / 2 ^ P.logArity i)) (idx % 2 ^ P.logArity i) :=
  ofIndexed_apply
    (fun _ ha _ hb hab => (pointOfIndex_inj P.prim (Nat.sub_le _ _) ha hb).mp hab) _ hidx

theorem isCodeword_finalWord (coeffs : List F) :
    IsCodeword (P.ldt.domain P.ldt.rounds) (P.ldt.degree P.ldt.rounds) (P.finalWord coeffs) := by
  refine ⟨polyOfCoeffs (coeffs.take P.finalDegree), ?_, fun x _ => rfl⟩
  have hlen : (coeffs.take P.finalDegree).length ≤ P.finalDegree := List.length_take_le _ _
  rw [ldt_degree, ldt_rounds, show P.cum P.rounds = P.arities.sum from Fri.cumLogArity_length _,
    Nat.sub_self, pow_zero, one_mul]
  exact (degree_polyOfCoeffs_lt _).trans_le (by exact_mod_cast hlen)

/-- Unique index `< 2 ^ P.n` whose domain point is `x` (`0` outside the domain). -/
def indexOf (x : F) : ℕ :=
  if h : ∃ i < 2 ^ P.n, pointOfIndex P.ω P.n P.n i = x then Nat.find h else 0

theorem indexOf_lt (x : F) : P.indexOf x < 2 ^ P.n := by
  unfold indexOf
  split_ifs with h
  · exact (Nat.find_spec h).1
  · positivity

theorem pointOfIndex_indexOf {x : F} (hx : x ∈ twoAdicDomain P.ω P.n 0) :
    pointOfIndex P.ω P.n P.n (P.indexOf x) = x := by
  have h : ∃ i < 2 ^ P.n, pointOfIndex P.ω P.n P.n i = x := by
    have hx' : x ∈ twoAdicDomain P.ω P.n (P.n - P.n) := by simpa using hx
    exact exists_pointOfIndex_eq P.prim le_rfl hx'
  rw [indexOf, dite_eq_left h]
  exact (Nat.find_spec h).2

end Read

/-! ## 2. Arithmetic and compiled multi-arity tensor verifier -/

def opened (pf : MultiProof F D P.batches P.queries) (t : Fin P.queries) (j : ℕ)
    (k : Fin (P.numClaims j)) : F :=
  entry ((pf.inputRows (P.slot j k).batch t)[(P.slot j k).matrix]?) (P.slot j k).col

def reducedTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (msg : Msg F D P.batches) (opened : ∀ j, Fin (P.numClaims j) → F)
    (r : TensorChal F W M) (index j : ℕ) : F :=
  ∑ k : Fin (P.numClaims j),
    tensorCoordWeight r (coord j k) *
      ((msg.value j k - opened j k) /
        (msg.point j k - P.shift * pointOfIndex P.ω P.n (P.n - P.cum j) (index >>> P.cum j)))

def foldChainMulti (P : MultiParams F) (ro : ℕ → F) (sibs : ℕ → Array F) (β : ℕ → F)
    (index : ℕ) : ℕ → F
  | 0 => ro 0
  | i + 1 =>
    let a := P.logArity i
    let c := P.cum i
    let groupIdx := index >>> (c + a)
    let idxInGroup := (index >>> c) % 2 ^ a
    let row := placeRowMultiM (2 ^ a) (foldChainMulti P ro sibs β index i) (sibs i) idxInGroup
    foldRowMultiM P.ω P.n a c groupIdx (β i) row + β i ^ (2 ^ a) * ro (i + 1)

def foldedTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) : F :=
  P.foldChainMulti (P.reducedTensor W M coord msg₀ (P.opened pf t) r index)
    (fun i => pf.siblings i t) β index i

def commitRowTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) : Array F :=
  placeRowMultiM (2 ^ P.logArity i) (P.foldedTensor W M coord pf msg₀ r β index t i)
    (pf.siblings i t) ((index >>> P.cum i) % 2 ^ P.logArity i)

theorem foldedTensor_zero (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) :
    P.foldedTensor W M coord pf msg₀ r β index t 0 =
      P.reducedTensor W M coord msg₀ (P.opened pf t) r index 0 := rfl

theorem foldedTensor_succ (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) :
    P.foldedTensor W M coord pf msg₀ r β index t (i + 1) =
      foldRowMultiM P.ω P.n (P.logArity i) (P.cum i) (index >>> (P.cum i + P.logArity i)) (β i)
          (P.commitRowTensor W M coord pf msg₀ r β index t i) +
        β i ^ (2 ^ P.logArity i) *
          P.reducedTensor W M coord msg₀ (P.opened pf t) r index (i + 1) := rfl

section Verifier

variable [DecidableEq F] [DecidableEq D]

def inputChecks {M' : Type} {C : ℕ → Type} (pf : MultiProof F D P.batches P.queries)
    (msg₀ : Msg F D P.batches) (index : Fin P.queries → ℕ) :
    List (OracleComp (MerkleAnswer M' C F D) Bool) :=
  (List.finRange P.batches).map fun b =>
    verifyOpeningsM (msg₀.inputRoots b) (P.dims b)
      (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
      (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))

def commitChecksTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    List (OracleComp (MerkleAnswer M' C F D) Bool) :=
  (List.range P.rounds).map fun i =>
    verifyOpeningsM (msg (i + 1)).commitRoot (P.commitDims i)
      (Array.ofFn fun t => index t >>> P.cum (i + 1))
      (Array.ofFn fun t => #[P.commitRowTensor W M coord pf (msg 0) r β (index t) t i])
      (Array.ofFn (pf.commitPaths i))

def FinalCheckTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) : Prop :=
  ∀ t, P.foldedTensor W M coord pf (msg 0) r β (index t) t P.rounds =
    hornerEval ((msg (P.rounds + 1)).finalCoeffs.take P.finalDegree)
      (pointOfIndex P.ω P.n (P.n - P.arities.sum) (index t >>> P.arities.sum))

instance (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    Decidable (P.FinalCheckTensor W M coord pf msg r β index) := by
  unfold FinalCheckTensor
  infer_instance

/-- **Compiled multi-arity tensor verifier**, making only Merkle hash queries. -/
def verifyWithTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    OracleComp (MerkleAnswer M' C F D) Bool :=
  (allM (P.inputChecks pf (msg 0) index)).bind fun ok =>
    if ok && decide (P.FinalCheckTensor W M coord pf msg r β index) then
      allM (P.commitChecksTensor W M coord pf msg r β index)
    else .pure false

theorem queryBound_verifyWithTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : MultiProof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    (P.verifyWithTensor (M' := M') (C := C) W M coord pf msg r β index).QueryBound
      P.verifierQueries := by
  have hin : (allM (P.inputChecks (M' := M') (C := C) pf (msg 0) index)).QueryBound
      (P.batches * (P.queries * (3 * P.n + 1))) := by
    have h := queryBound_allM (n := P.queries * (3 * P.n + 1))
      (P.inputChecks (M' := M') (C := C) pf (msg 0) index) fun c hc => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
        refine (queryBound_verifyOpeningsM _ _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        exact Nat.mul_le_mul_left _ (by have := P.height_le b; omega)
    rwa [inputChecks, List.length_map, List.length_finRange] at h
  have hcommit :
      (allM (P.commitChecksTensor (M' := M') (C := C) W M coord pf msg r β index)).QueryBound
        (P.rounds * (P.queries * (3 * P.n + 1))) := by
    have h := queryBound_allM (n := P.queries * (3 * P.n + 1))
      (P.commitChecksTensor (M' := M') (C := C) W M coord pf msg r β index) fun c hc => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
        refine (queryBound_verifyOpeningsM _ _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        refine Nat.mul_le_mul_left _ ?_
        have : Merkle.maxLogHeight (P.commitDims i).toList ≤ P.n := by
          simp only [commitDims, List.toList_toArray, Merkle.maxLogHeight]
          omega
        omega
    rwa [commitChecksTensor, List.length_map, List.length_range] at h
  refine QueryBound.mono (hin.bind fun ok => ?_) (by rw [verifierQueries, Nat.add_mul])
  split
  · exact hcommit
  · exact queryBound_pure _ _

theorem run_verifyWithTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (f : ∀ x : FSQuery M' C (HashQuery F D), MerkleAnswer M' C F D x)
    (pf : MultiProof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    (P.verifyWithTensor W M coord pf msg r β index).run f =
      (((List.finRange P.batches).all fun b =>
          Merkle.verifyOpenings (hasherOf f) ((msg 0).inputRoots b) (P.dims b)
            (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
            (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))) &&
        decide (P.FinalCheckTensor W M coord pf msg r β index) &&
        (List.range P.rounds).all fun i =>
          Merkle.verifyOpenings (hasherOf f) (msg (i + 1)).commitRoot (P.commitDims i)
            (Array.ofFn fun t => index t >>> P.cum (i + 1))
            (Array.ofFn fun t => #[P.commitRowTensor W M coord pf (msg 0) r β (index t) t i])
            (Array.ofFn (pf.commitPaths i))) := by
  rw [verifyWithTensor, run_bind, run_allM, inputChecks, List.all_map]
  simp only [Function.comp_def, run_verifyOpeningsM]
  split
  · next h =>
    rw [run_allM, commitChecksTensor, List.all_map]
    simp only [Function.comp_def, run_verifyOpeningsM]
    rw [h, Bool.true_and]
  · next h =>
    rw [run_pure, (Bool.not_eq_true _).mp h, Bool.false_and]

noncomputable def verifyGrindViewTensor {M' : Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches) (pf : MultiProof F D P.batches P.queries)
    (t : Transcript M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (P.rounds + 2)) :
    OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D)
      Bool :=
  @ite _ (PowPasses t) (Classical.propDecidable _)
    (P.verifyWithTensor W M coord pf (fun j => view (msgAt (ungrind t) j))
      (tensorOfMulti (ungrind t)) (betasOfTensorMulti (ungrind t))
      (fun k => P.indexOf (queriesOfTensorMulti (ungrind t) k)))
    (.pure false)

theorem queryBound_verifyGrindViewTensor {M' : Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches) (pf : MultiProof F D P.batches P.queries)
    (t : Transcript M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (P.rounds + 2)) :
    (P.verifyGrindViewTensor W M coord bits view pf t).QueryBound P.verifierQueries := by
  unfold verifyGrindViewTensor
  split
  · exact P.queryBound_verifyWithTensor W M coord pf _ _ _ _
  · exact queryBound_pure _ _

theorem run_verifyGrindViewTensor {M' : Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches)
    (f : ∀ x, MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D x)
    (pf : MultiProof F D P.batches P.queries)
    (t : Transcript M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (P.rounds + 2)) :
    (P.verifyGrindViewTensor W M coord bits view pf t).run f = true ↔
      PowPasses t ∧
        (P.verifyWithTensor
          (M' := M') (C := GrindChal bits (ChalTensorMulti P.ldt W M P.queries))
          W M coord pf (fun j => view (msgAt (ungrind t) j)) (tensorOfMulti (ungrind t))
          (betasOfTensorMulti (ungrind t))
          (fun k => P.indexOf (queriesOfTensorMulti (ungrind t) k))).run f = true := by
  unfold verifyGrindViewTensor
  split
  · next h => exact ⟨fun hr => ⟨h, hr⟩, fun hr => hr.2⟩
  · next h => exact ⟨fun hr => absurd hr (by simp), fun hr => absurd hr.1 h⟩

end Verifier

/-! ## 3. Accepting run implies oracle-model acceptance (`AcceptsTensorMulti`) -/

section Accepts

variable [DecidableEq F] [DecidableEq D]

omit [DecidableEq F] [DecidableEq D] in
theorem queriesOfTensorMulti_mem {M' : Type} {S : MultiLdtInstance F} {W M q : ℕ}
    (t : Transcript M' (ChalTensorMulti S W M q) (S.rounds + 2)) (k : Fin q) :
    queriesOfTensorMulti t k ∈ S.domain 0 := by
  cases t with
  | snoc t m c =>
    rw [PcsRbr.queriesOfTensorMulti_snoc,
      PcsRbr.ChalTensorMulti.points_of_not_le (Nat.not_succ_le_self _)]
    exact (PcsRbr.chalTensorMultiQuery _ c k).2

variable {M' : Type} {C : ℕ → Type} [DecidableEq (FSQuery M' C (HashQuery F D))]
  {W M : ℕ} {coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W}
  {pf : MultiProof F D P.batches P.queries} {msg : ℕ → Msg F D P.batches}
  {r : TensorChal F W M} {β : ℕ → F} {index : Fin P.queries → ℕ}
  {l l' : Log (MerkleAnswer M' C F D)}

theorem outcome_verifyWithTensor
    (h : Outcome (P.verifyWithTensor W M coord pf msg r β index) l true l') :
    (∀ b t, Opens l' ((msg 0).inputRoots b) (P.dims b)
        (index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) (pf.inputRows b t)) ∧
      P.FinalCheckTensor W M coord pf msg r β index ∧
      ∀ i < P.rounds, ∀ t, Opens l' (msg (i + 1)).commitRoot (P.commitDims i)
        (index t >>> P.cum (i + 1))
        #[P.commitRowTensor W M coord pf (msg 0) r β (index t) t i] := by
  obtain ⟨ok, l₁, hin, hrest⟩ := outcome_bind.mp h
  split at hrest
  · next hcond =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨rfl, hfinal⟩ := hcond
    refine ⟨fun b t => ?_, hfinal, fun i hi t => ?_⟩
    · obtain ⟨la, lb, hrun, hpre⟩ := outcome_allM hin _
        (List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩)
      exact ((opens_of_outcome_ofFn hrun t).of_prefix hpre).of_prefix hrest.prefix
    · obtain ⟨la, lb, hrun, hpre⟩ := outcome_allM hrest _
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      exact (opens_of_outcome_ofFn hrun t).of_prefix hpre
  · exact absurd hrest.1 (by simp)

omit [DecidableEq D] in
theorem pcsInputTensor_eq_reducedTensor (hl : ¬ LogCollision hashObs l')
    {idx : ℕ} {t : Fin P.queries}
    (hopen : ∀ b, Opens l' ((msg 0).inputRoots b) (P.dims b)
      (idx >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) (pf.inputRows b t))
    (hidx : idx < 2 ^ P.n) {j : ℕ} (hj : j ≤ P.rounds) :
    pcsInputTensor P.shift coord (P.claims (msg 0) (committedRow l')) r j
        (pointOfIndex P.ω P.n (P.n - P.cum j) (idx >>> P.cum j)) =
      P.reducedTensor W M coord (msg 0) (P.opened pf t) r idx j := by
  have hjn : P.cum j ≤ P.n := P.cum_le_n j
  unfold pcsInputTensor reducedOpeningTensor MultiParams.reducedTensor quotientAt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn)]
  obtain ⟨d, hd, hdh, -⟩ := P.slot_dims j hj k
  have hdh' : d.logHeight = P.n - P.cum j := hdh
  have hmem : d ∈ (P.dims (P.slot j k).batch).toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hd)
  have hle := Merkle.le_maxLogHeight hmem
  have hH := P.height_le (P.slot j k).batch
  have hrow := committedRow_of_opens hl (hopen (P.slot j k).batch) hd
  rw [← Nat.shiftRight_add, show P.n - Merkle.maxLogHeight (P.dims (P.slot j k).batch).toList +
    (Merkle.maxLogHeight (P.dims (P.slot j k).batch).toList - d.logHeight) = P.cum j by omega] at hrow
  rw [hrow]
  rfl

omit [DecidableEq D] in
/-- **Multi-arity folding round from a committed row opening:**
in a collision-free log, an opened `2 ^ a`-entry row `row` at `idx >>> cum (i + 1)`
fixes the committed codeword `P.commitWord i` on the entire `2 ^ a`-coset, so:
1. `commitWord` at `idx >>> cum i` equals `row.getD ((idx >>> cum i) % 2 ^ a) 0`;
2. `foldAtPow` of `commitWord` equals `foldRowMultiM` of `row`! -/
theorem round_of_opens (hl : ¬ LogCollision hashObs l') {i : ℕ} (hi : i < P.rounds)
    {root : D} {idx : ℕ} (hidx : idx < 2 ^ P.n) {row : Array F}
    (hopen : Opens l' root (P.commitDims i) (idx >>> P.cum (i + 1)) #[row]) (β : F) :
    let w := P.commitWord i (committedRow l' root (P.commitDims i) 0)
    w (pointOfIndex P.ω P.n (P.n - P.cum i) (idx >>> P.cum i)) =
        row.getD ((idx >>> P.cum i) % 2 ^ P.logArity i) 0 ∧
      foldAtPow (P.ldt.zeta i) (2 ^ P.logArity i) w β
          (pointOfIndex P.ω P.n (P.n - P.cum i) (idx >>> P.cum i)) =
        foldRowMultiM P.ω P.n (P.logArity i) (P.cum i) (idx >>> (P.cum i + P.logArity i)) β
          row := by
  intro w
  have ha : 0 < P.logArity i := P.logArity_pos hi
  have hcum_succ : P.cum (i + 1) = P.cum i + P.logArity i := P.cum_succ hi
  have hka : P.cum i + P.logArity i ≤ P.n := hcum_succ ▸ P.cum_le_n (i + 1)
  have hrow : committedRow l' root (P.commitDims i) 0 (idx >>> P.cum (i + 1)) = some row :=
    committedRow_of_opens_single hl hopen
  set a := P.logArity i
  set c := P.cum i
  set groupIdx := idx >>> (c + a)
  have hgroup_eq : idx >>> P.cum (i + 1) = groupIdx := by rw [hcum_succ]
  rw [hgroup_eq] at hrow
  have hgroup_lt : groupIdx < 2 ^ (P.n - (c + a)) := shiftRight_lt_two_pow hidx hka
  have hdiv_eq : (idx >>> c) / 2 ^ a = groupIdx := by
    dsimp only [groupIdx]
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  have hw_coset : ∀ r < 2 ^ a,
      row.getD r 0 = w (pointOfIndex P.ω P.n (P.n - c) (groupIdx * 2 ^ a + r)) := by
    intro r hr
    have hchild_lt : groupIdx * 2 ^ a + r < 2 ^ (P.n - c) := by
      have hexp : 2 ^ (P.n - c) = 2 ^ (P.n - (c + a)) * 2 ^ a := by
        rw [← pow_add]; congr 1; omega
      rw [hexp]
      have h1 : groupIdx * 2 ^ a + r < groupIdx * 2 ^ a + 2 ^ a := Nat.add_lt_add_left hr _
      have h2 : groupIdx * 2 ^ a + 2 ^ a = (groupIdx + 1) * 2 ^ a := by ring
      have h3 : (groupIdx + 1) * 2 ^ a ≤ 2 ^ (P.n - (c + a)) * 2 ^ a :=
        Nat.mul_le_mul_right _ hgroup_lt
      omega
    have hq : (groupIdx * 2 ^ a + r) / 2 ^ a = groupIdx := by
      rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hr, Nat.add_zero]
    have hm : (groupIdx * 2 ^ a + r) % 2 ^ a = r := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    dsimp only [w]
    rw [P.commitWord_apply i _ hchild_lt, hq, hm, hrow]
    rfl
  refine ⟨?_, ?_⟩
  · have hlt_c : idx >>> c < 2 ^ (P.n - c) := shiftRight_lt_two_pow hidx (by omega)
    dsimp only [w]
    rw [P.commitWord_apply i _ hlt_c, hdiv_eq, hrow]
    rfl
  · rw [foldRowMultiM_eq_foldAtPow P.prim ha hka w β row hw_coset]
    have hprim : IsPrimitiveRoot (P.ω ^ 2 ^ (P.n - a)) (2 ^ a) :=
      Domain.isPrimitiveRoot_generator P.prim (by omega)
    have hx_ne : pointOfIndex P.ω P.n (P.n - c) (idx >>> c) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (P.prim.ne_zero (by positivity)))
    have hpow_eq :
        pointOfIndex P.ω P.n (P.n - c) (idx >>> c) ^ 2 ^ a =
          pointOfIndex P.ω P.n (P.n - c) (groupIdx * 2 ^ a) ^ 2 ^ a := by
      rw [pointOfIndex_pow_two_pow P.prim (by omega) (by omega),
        pointOfIndex_pow_two_pow P.prim (by omega) (by omega)]
      have hL : (idx >>> c) >>> a = groupIdx := by
        rw [Nat.shiftRight_eq_div_pow]; exact hdiv_eq
      have hR : (groupIdx * 2 ^ a) >>> a = groupIdx := by
        rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos a)]
      rw [hL, hR]
    exact foldAtPow_eq_of_pow_eq hprim (Nat.two_pow_pos a) w β hx_ne hpow_eq

theorem queryAcceptsMulti_of_outcome_tensor
    (hrun : Outcome (P.verifyWithTensor W M coord pf msg r β index) l true l')
    (hl : ¬ LogCollision hashObs l') (t : Fin P.queries) (hindex : index t < 2 ^ P.n)
    (words : ℕ → F → F)
    (hwords : ∀ i ≤ P.rounds, words i = (P.read (i + 1) (msg (i + 1)) (committedRow l')).word) :
    QueryAcceptsMulti P.ldt
      (pcsInputTensor P.shift coord (P.claims (msg 0) (committedRow l')) r)
      words β (pointOfIndex P.ω P.n P.n (index t)) := by
  obtain ⟨hin, hfinal, hcommit⟩ := P.outcome_verifyWithTensor hrun
  have hpow : ∀ j ≤ P.rounds,
      pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.ldt.cumLog j =
        pointOfIndex P.ω P.n (P.n - P.cum j) (index t >>> P.cum j) := fun j hj => by
    rw [P.ldt_cumLog hj]
    exact pointOfIndex_pow_two_pow P.prim le_rfl (P.cum_le_n j) (index t)
  have hro : ∀ j ≤ P.rounds,
      pcsInputTensor P.shift coord (P.claims (msg 0) (committedRow l')) r j
          (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.ldt.cumLog j) =
        P.reducedTensor W M coord (msg 0) (P.opened pf t) r (index t) j := fun j hj => by
    rw [hpow j hj]
    exact P.pcsInputTensor_eq_reducedTensor hl (fun b => hin b t) hindex hj
  have hround : ∀ i < P.rounds,
      words i (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.ldt.cumLog i) =
          P.foldedTensor W M coord pf (msg 0) r β (index t) t i ∧
        foldAtPow (P.ldt.zeta i) (2 ^ P.ldt.logArity i) (words i) (β i)
            (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.ldt.cumLog i) =
          foldRowMultiM P.ω P.n (P.logArity i) (P.cum i)
            (index t >>> (P.cum i + P.logArity i)) (β i)
            (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i) := fun i hi => by
    obtain ⟨hval, hfold⟩ := P.round_of_opens hl hi hindex (hcommit i hi t) (β i)
    rw [hpow i hi.le, hwords i hi.le, P.read_word_of_lt hi]
    refine ⟨hval.trans ?_, hfold⟩
    exact placeRowMultiM_self (Nat.mod_lt _ (Nat.two_pow_pos _)) _ _
  have hlast : words P.rounds (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.ldt.cumLog P.rounds) =
      P.foldedTensor W M coord pf (msg 0) r β (index t) t P.rounds := by
    rw [hpow _ le_rfl, show P.cum P.rounds = P.arities.sum from Fri.cumLogArity_length _,
      hwords _ le_rfl, P.read_word_last, hfinal t, hornerEval_eq_eval]
    rfl
  have hword : ∀ i ≤ P.rounds,
      words i (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.ldt.cumLog i) =
        P.foldedTensor W M coord pf (msg 0) r β (index t) t i := fun i hi => by
    rcases Nat.lt_or_ge i P.rounds with hlt | hge
    · exact (hround i hlt).1
    · obtain rfl : i = P.rounds := le_antisymm hi hge
      exact hlast
  refine ⟨?_, fun i hi => ?_⟩
  · have h0 := hword 0 (Nat.zero_le _)
    have hro0 := hro 0 (Nat.zero_le _)
    rw [MultiLdtInstance.cumLog_zero, pow_zero, pow_one] at h0 hro0
    rw [h0, hro0, P.foldedTensor_zero]
  · rw [hword (i + 1) hi, (hround i hi).2, hro (i + 1) hi, P.foldedTensor_succ]
    rfl

theorem acceptsTensorMulti_of_outcome_verifyWithTensor_view {M'' : Type}
    (view : M'' → Msg F D P.batches)
    (t : Transcript M'' (ChalTensorMulti P.ldt W M P.queries) (P.rounds + 2))
    (hrun : Outcome (P.verifyWithTensor (M' := M') (C := C) W M coord pf
      (fun j => view (msgAt t j)) (tensorOfMulti t) (betasOfTensorMulti t)
      fun k => P.indexOf (queriesOfTensorMulti t k)) l true l')
    (hl : ¬ LogCollision hashObs l') :
    AcceptsTensorMulti P.ldt P.shift coord
      (t.mapIdx fun j m => P.read j (view m) (committedRow l')) := by
  have hwords : ∀ i ≤ P.rounds,
      wordsOf (t.mapIdx fun j m => P.read j (view m) (committedRow l')) i =
        (P.read (i + 1) (view (msgAt t (i + 1))) (committedRow l')).word := fun i hi =>
    PcsRbr.wordsOf_mapIdx _ t (getElem?_msgs t (by omega))
  have hclaims : claimsOf (t.mapIdx fun j m => P.read j (view m) (committedRow l')) =
      P.claims (view (msgAt t 0)) (committedRow l') :=
    PcsRbr.claimsOf_mapIdx _ t (getElem?_msgs t (Nat.zero_le _))
  refine ⟨?_, fun k => ?_⟩
  · have h := P.isCodeword_finalWord (view (msgAt t (P.rounds + 1))).finalCoeffs
    rw [← P.read_word_last _ (committedRow l'), ← hwords _ le_rfl] at h
    exact h
  · have hx : queriesOfTensorMulti t k ∈ twoAdicDomain P.ω P.n 0 :=
      queriesOfTensorMulti_mem (S := P.ldt) t k
    rw [hclaims, PcsRbr.tensorOfMulti_mapIdx, PcsRbr.betasOfTensorMulti_mapIdx,
      PcsRbr.queriesOfTensorMulti_mapIdx, ← P.pointOfIndex_indexOf hx]
    exact P.queryAcceptsMulti_of_outcome_tensor hrun hl k (P.indexOf_lt _) _ hwords

omit [DecidableEq F] [DecidableEq D] in
private theorem queryAcceptsMulti_of_input_eq {S : MultiLdtInstance F}
    {ro ro' words : ℕ → F → F} {β : ℕ → F} {x : F}
    (h : ∀ j ≤ S.rounds, ro' j (x ^ 2 ^ S.cumLog j) = ro j (x ^ 2 ^ S.cumLog j))
    (hq : QueryAcceptsMulti S ro words β x) :
    QueryAcceptsMulti S ro' words β x := by
  refine ⟨?_, fun i hi => ?_⟩
  · have h0 := h 0 (Nat.zero_le _)
    rw [MultiLdtInstance.cumLog_zero, pow_zero, pow_one] at h0
    rw [h0]
    exact hq.1
  · rw [h (i + 1) hi]
    exact hq.2 i hi

omit [DecidableEq D] in
private theorem pcsInputTensor_congr_of_rows (msg : Msg F D P.batches)
    (r : TensorChal F W M) {c c' : Committed F D} {idx : ℕ} (hidx : idx < 2 ^ P.n)
    (hc : ∀ (b : Fin P.batches) (mi : ℕ) (d : Dimensions), (P.dims b)[mi]? = some d →
      c (msg.inputRoots b) (P.dims b) mi (idx >>> (P.n - d.logHeight)) =
        c' (msg.inputRoots b) (P.dims b) mi (idx >>> (P.n - d.logHeight)))
    {j : ℕ} (hj : j ≤ P.rounds) :
    pcsInputTensor P.shift coord (P.claims msg c) r j
        (pointOfIndex P.ω P.n (P.n - P.cum j) (idx >>> P.cum j)) =
      pcsInputTensor P.shift coord (P.claims msg c') r j
        (pointOfIndex P.ω P.n (P.n - P.cum j) (idx >>> P.cum j)) := by
  have hjn : P.cum j ≤ P.n := P.cum_le_n j
  unfold pcsInputTensor reducedOpeningTensor quotientAt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn),
    P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn)]
  obtain ⟨d, hd, hdh, -⟩ := P.slot_dims j hj k
  have hdh' : d.logHeight = P.n - P.cum j := hdh
  have hrow := hc (P.slot j k).batch (P.slot j k).matrix d hd
  rw [show P.n - d.logHeight = P.cum j by omega] at hrow
  rw [hrow]
  rfl

/-- **Base-field committed-row multi-arity oracle acceptance** (counterpart of
`AcceptsComTensor.lean`, used directly by multi-arity STARK soundness). -/
theorem acceptsTensorMulti_of_outcome_verifyWithTensor_view_com {M'' : Type}
    (view : M'' → Msg F D P.batches)
    (t : Transcript M'' (ChalTensorMulti P.ldt W M P.queries) (P.rounds + 2))
    (hrun : Outcome (P.verifyWithTensor (M' := M') (C := C) W M coord pf
      (fun j => view (msgAt t j)) (tensorOfMulti t) (betasOfTensorMulti t)
      fun k => P.indexOf (queriesOfTensorMulti t k)) l true l')
    (hl : ¬ LogCollision hashObs l') (c : Committed F D)
    (hc : ∀ (b : Fin P.batches) (k : Fin P.queries) (mi : ℕ) (d : Dimensions),
      (P.dims b)[mi]? = some d →
      c ((view (msgAt t 0)).inputRoots b) (P.dims b) mi
          (P.indexOf (queriesOfTensorMulti t k) >>> (P.n - d.logHeight)) =
        committedRow l' ((view (msgAt t 0)).inputRoots b) (P.dims b) mi
          (P.indexOf (queriesOfTensorMulti t k) >>> (P.n - d.logHeight))) :
    AcceptsTensorMulti P.ldt P.shift coord
      (t.mapIdx fun j m =>
        if j = 0 then P.read 0 (view m) c else P.read j (view m) (committedRow l')) := by
  have hwords : ∀ i ≤ P.rounds,
      wordsOf (t.mapIdx fun j m =>
          if j = 0 then P.read 0 (view m) c else P.read j (view m) (committedRow l')) i =
        (P.read (i + 1) (view (msgAt t (i + 1))) (committedRow l')).word := fun i hi => by
    rw [PcsRbr.wordsOf_mapIdx _ t (getElem?_msgs t (by omega)), ite_eq_right (Nat.succ_ne_zero i)]
  have hclaims : claimsOf (t.mapIdx fun j m =>
        if j = 0 then P.read 0 (view m) c else P.read j (view m) (committedRow l')) =
      P.claims (view (msgAt t 0)) c := by
    rw [PcsRbr.claimsOf_mapIdx _ t (getElem?_msgs t (Nat.zero_le _)), ite_eq_left rfl,
      P.read_claims_zero]
  refine ⟨?_, fun k => ?_⟩
  · have h := P.isCodeword_finalWord (view (msgAt t (P.rounds + 1))).finalCoeffs
    rw [← P.read_word_last _ (committedRow l'), ← hwords _ le_rfl] at h
    exact h
  · have hx : queriesOfTensorMulti t k ∈ twoAdicDomain P.ω P.n 0 :=
      queriesOfTensorMulti_mem (S := P.ldt) t k
    rw [hclaims, PcsRbr.tensorOfMulti_mapIdx, PcsRbr.betasOfTensorMulti_mapIdx,
      PcsRbr.queriesOfTensorMulti_mapIdx, ← P.pointOfIndex_indexOf hx]
    refine queryAcceptsMulti_of_input_eq (fun j hj => ?_)
      (P.queryAcceptsMulti_of_outcome_tensor hrun hl k (P.indexOf_lt _) _ hwords)
    rw [P.ldt_cumLog hj, pointOfIndex_pow_two_pow P.prim le_rfl (P.cum_le_n j)]
    exact P.pcsInputTensor_congr_of_rows _ _ (P.indexOf_lt _)
      (fun b mi d hd => hc b k mi d hd) hj

theorem acceptsTensorMulti_of_outcome_verifyGrindViewTensor {M'' : Type} {bits : ℕ → ℕ}
    [DecidableEq (FSQuery M'' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (HashQuery F D))]
    {view : M'' → Msg F D P.batches}
    {t : Transcript M'' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (P.rounds + 2)}
    {l l' : Log (MerkleAnswer M'' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D)}
    (hrun : Outcome (P.verifyGrindViewTensor W M coord bits view pf t) l true l')
    {digests : ℕ → M'' → List D} {r : ℕ}
    (hno : ¬ HasBad (Hit digests r) l') :
    PowPasses t ∧
      AcceptsTensorMulti P.ldt P.shift coord
        ((ungrind t).mapIdx fun j m => P.read j (view m) (committedRow l')) := by
  unfold verifyGrindViewTensor at hrun
  split at hrun
  · next hpow =>
    exact ⟨hpow, P.acceptsTensorMulti_of_outcome_verifyWithTensor_view view (ungrind t) hrun
      (not_logCollision_of_not_hasBad_hit hno)⟩
  · exact absurd hrun.1 (by simp)

end Accepts

/-! ## 4. Chained-ROM Soundness -/

section ChainedSoundness

variable [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D] [DecidableEq D]

noncomputable def experimentGrindViewTensor {M' : Type} [DecidableEq M'] (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches) {A : Type*}
    (adv : OracleComp
      (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D) A)
    (msgs : A → ℕ → M') (proofOf : A → MultiProof F D P.batches P.queries) :
    OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D)
      (A × Bool) :=
  (fsExperiment (P.rounds + 2) adv msgs).bind fun out =>
    (P.verifyGrindViewTensor W M coord bits view (proofOf out.1) out.2).bind fun b =>
      .pure (out.1, b)

/-- **Soundness of compiled multi-arity tensor-batched FRI (chained ROM).** -/
theorem soundness_grind_view_tensorMulti_of_imp {M' : Type} [DecidableEq M'] (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (hinj : ∀ j ≤ P.rounds, Function.Injective (coord j))
    (bits : ℕ → ℕ) (view : M' → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ)
    {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) W M θ (εα j))
    (hε₀ : ∀ j ≤ P.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < P.rounds,
      StepMCAArity (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1))
        (P.ldt.degree (i + 1)) θ (εβ i))
    (hα : ε₀ / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp
      (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (msgs : A → ℕ → M')
    (proofOf : A → MultiProof F D P.batches P.queries)
    (E : A → Log
      (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D) → Prop)
    (hE : ∀ (out : A × Transcript M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries))
        (P.rounds + 2))
      (l : Log (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D))
      (b : Bool)
      (l' : Log (MerkleAnswer M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l →
      Outcome (P.verifyGrindViewTensor W M coord bits view (proofOf out.1) out.2) l b l' →
      E out.1 l' → b = true) :
    prob (fun res l => E res.1 l ∧
        ClaimsFailMulti P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindViewTensor W M coord bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  have : ∀ i, Nonempty (ChalTensorMulti P.ldt W M P.queries i) :=
    PcsRbr.ChalTensorMulti.nonempty P.domain_zero_nonempty W M P.queries
  have hε : ∀ i < P.rounds + 2,
      roundErrorTensor P.rounds ε₀ εβ θ P.queries i / 2 ^ bits i ≤ εmax := by
    intro i hi
    rcases i with _ | k
    · exact hα
    · by_cases hk : k < P.rounds
      · rw [PcsRbr.roundErrorTensor_succ_of_lt hk]; exact hβ k hk
      · obtain rfl : k = P.rounds := by omega
        rw [PcsRbr.roundErrorTensor_last]; exact hq
  have hnd : ∀ t : Transcript (PcsRbr.Msg F P.numClaims)
      (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (P.rounds + 2),
      PowPasses t → ClaimsFailMulti P.ldt P.shift θ (claimsOf (ungrind t)) →
        AcceptsTensorMulti P.ldt P.shift coord (ungrind t) →
          ¬ PcsRbr.grindDoomed bits (PcsRbr.doomedTensorMulti P.ldt P.shift coord θ P.queries)
              (P.rounds + 2) t :=
    fun t => PcsRbr.not_grindDoomedTensorMulti_of_accepts t
  have h := prob_fsExperiment_bind_committedRow_le (r := P.rounds + 2)
    (PcsRbr.rbrSound_grind_tensorMulti P.ldt P.shift_ne coord hinj hθ P.queries bits hmca hε₀ hstep)
    hε ((div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq)
    (PcsRbr.grindDoomedTensorMulti_nil bits)
    (digestsOf := fun j m => digestsOfAt P.rounds j (view m)) (M := P.batches + P.rounds)
    (fun x => length_chalDigests_le P.rounds view x)
    (read := fun j m c => P.read j (view m) c)
    (fun j m c c' hc => P.read_congr j (view m) c c' hc)
    hadv msgs
    (rest := fun out =>
      (P.verifyGrindViewTensor W M coord bits view (proofOf out.1) out.2).bind fun b =>
        .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (P.queryBound_verifyGrindViewTensor W M coord bits view _ _).bind (m := 0) fun _ =>
      queryBound_pure _ _)
    (E := fun res l => E res.1 l ∧
      ClaimsFailMulti P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
    fun out l res l' hexp hrun hres hno => by
      obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      obtain rfl : b = true := hE out l b _ hexp hver hres.1
      obtain ⟨hpow, hacc⟩ := P.acceptsTensorMulti_of_outcome_verifyGrindViewTensor hver hno
      refine hnd _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow) ?_ ?_
      · have h0 : (ungrind out.2).msgs[0]? = some (msgs out.1 0) := by
          rw [msgs_ungrind, msgs_of_outcome_fsExperiment hexp, List.getElem?_map,
            List.getElem?_range (Nat.succ_pos _)]
          rfl
        rw [PcsRbr.ungrind_mapIdx, PcsRbr.claimsOf_mapIdx _ (ungrind out.2) h0]
        exact hres.2
      · rw [PcsRbr.ungrind_mapIdx]
        exact hacc
  rwa [show ((P.rounds + 2 : ℕ) : ℝ) = (P.rounds : ℝ) + 2 by push_cast; rfl] at h

end ChainedSoundness

end MultiParams

/-! ## 5. Single-root incremental sponge lift (`entryCap = 1`, `c = 3 / 2`) -/

section CompiledSpongeMulti

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

/-- Single-step message of the incremental sponge multi-arity protocol:
either an input batch root (steps `0 .. P.batches - 1`) or a full `PcsRbr.Msg`
for steps `P.batches .. P.batches + P.rounds + 1`. -/
structure StepMsgMulti (F : Type) (numClaims : ℕ → ℕ) where
  batchFn : ℕ → ℕ → ℕ → ℕ → F
  claims : ∀ j, Fin (numClaims j) → Claim F
  word : F → F

/-- Incremental sponge challenge type (`entryCap = 1`):
`PUnit` for the `P.batches` root-absorption steps, then `GrindChal bits (ChalTensorMulti ...)`. -/
def SpongeChalTensorMulti (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) (i : ℕ) : Type :=
  if i < P.batches then PUnit
  else GrindChal bits (ChalTensorMulti P.ldt W M P.queries) (i - P.batches)

instance (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) (i : ℕ) :
    Fintype (SpongeChalTensorMulti P W M bits i) := by
  unfold SpongeChalTensorMulti
  split_ifs
  · exact inferInstanceAs (Fintype PUnit)
  · exact inferInstanceAs
      (Fintype (GrindChal bits (ChalTensorMulti P.ldt W M P.queries) (i - P.batches)))

instance (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) (i : ℕ) :
    Nonempty (SpongeChalTensorMulti P W M bits i) := by
  have : ∀ k, Nonempty (ChalTensorMulti P.ldt W M P.queries k) :=
    PcsRbr.ChalTensorMulti.nonempty P.domain_zero_nonempty W M P.queries
  unfold SpongeChalTensorMulti
  split_ifs
  · exact ⟨()⟩
  · exact inferInstanceAs
      (Nonempty (GrindChal bits (ChalTensorMulti P.ldt W M P.queries) (i - P.batches)))

omit [Fintype F] in
private theorem spongeChalTensorMulti_add_eq (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ)
    (k : ℕ) :
    SpongeChalTensorMulti P W M bits (P.batches + k) =
      GrindChal bits (ChalTensorMulti P.ldt W M P.queries) k := by
  unfold SpongeChalTensorMulti
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

def spongeChalTensorMultiCast (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : SpongeChalTensorMulti P W M bits (P.batches + k)) :
    GrindChal bits (ChalTensorMulti P.ldt W M P.queries) k :=
  cast (spongeChalTensorMulti_add_eq P W M bits k) c

def spongeChalTensorMultiOf (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) k) :
    SpongeChalTensorMulti P W M bits (P.batches + k) :=
  cast (spongeChalTensorMulti_add_eq P W M bits k).symm c

omit [Fintype F] in
theorem spongeChalTensorMultiCast_of (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) k) :
    spongeChalTensorMultiCast P W M bits (spongeChalTensorMultiOf P W M bits c) = c := by
  simp [spongeChalTensorMultiCast, spongeChalTensorMultiOf]

omit [Fintype F] in
theorem spongeChalTensorMultiOf_cast (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : SpongeChalTensorMulti P W M bits (P.batches + k)) :
    spongeChalTensorMultiOf P W M bits (spongeChalTensorMultiCast P W M bits c) = c := by
  simp [spongeChalTensorMultiCast, spongeChalTensorMultiOf]

/-- Extract the committed column-entry function of batch `b` from the first
`P.batches` steps of a sponge transcript. -/
def extractBatchFnMulti (P : MultiParams F) {C : ℕ → Type} :
    {i : ℕ} → Transcript (StepMsgMulti F P.numClaims) C i → ℕ → ℕ → ℕ → ℕ → F
  | 0, _ => fun _ _ _ _ => 0
  | i + 1, .snoc t m _ =>
    if i < P.batches then Function.update (extractBatchFnMulti P t) i (m.batchFn i)
    else extractBatchFnMulti P t

/-- Assemble a `PcsRbr.Msg` at FRI round `k` from the batch functions accumulated
in steps `< P.batches` and step `P.batches + k`'s message `m`. -/
def extractStepPcsMsgMulti (P : MultiParams F) (bfn : ℕ → ℕ → ℕ → ℕ → F) (k : ℕ)
    (m : StepMsgMulti F P.numClaims) : PcsRbr.Msg F P.numClaims where
  claims := fun j c =>
    if k = 0 then
      { f := ofIndexed (2 ^ (P.n - P.cum j))
          (fun idx => P.shift * pointOfIndex P.ω P.n (P.n - P.cum j) idx)
          (fun idx => bfn (P.slot j c).batch.val (P.slot j c).matrix idx (P.slot j c).col)
        z := (m.claims j c).z
        y := (m.claims j c).y }
    else m.claims j c
  word := m.word

/-- Extract the `k`-round multi-arity `PcsRbr` transcript from a `(P.batches + k)`-step
incremental sponge transcript. -/
noncomputable def extractPcsTensorMulti (P : MultiParams F) (W M : ℕ) (bits : ℕ → ℕ) :
    (k : ℕ) →
      Transcript (StepMsgMulti F P.numClaims) (SpongeChalTensorMulti P W M bits) (P.batches + k) →
      Transcript (PcsRbr.Msg F P.numClaims)
        (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) k
  | 0, _ => .nil
  | k + 1, .snoc t m c =>
    (extractPcsTensorMulti P W M bits k t).snoc
      (extractStepPcsMsgMulti P (extractBatchFnMulti P t) k m)
      (spongeChalTensorMultiCast P W M bits c)

/-- Lifted round-by-round `doomed` predicate for the `(P.batches + P.rounds + 2)`-step
incremental sponge multi-arity tensor protocol. -/
def spongeDoomedTensorMulti (P : MultiParams F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ) (θ : ℝ) (i : ℕ)
    (t : Transcript (StepMsgMulti F P.numClaims) (SpongeChalTensorMulti P W M bits) i) : Prop :=
  if h : P.batches < i then
    PcsRbr.grindDoomed bits (PcsRbr.doomedTensorMulti P.ldt P.shift coord θ P.queries)
      (i - P.batches)
      (extractPcsTensorMulti P W M bits (i - P.batches)
        (cast (by rw [Nat.add_sub_of_le (Nat.le_of_lt h)]) t))
  else True

omit [Fintype F] in
theorem spongeDoomedTensorMulti_nil (P : MultiParams F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ) (θ : ℝ) :
    spongeDoomedTensorMulti P W M coord bits θ 0 .nil := by
  simp [spongeDoomedTensorMulti]

omit [Fintype F] in
theorem spongeDoomedTensorMulti_add_succ (P : MultiParams F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ) (θ : ℝ) (k : ℕ)
    (t : Transcript (StepMsgMulti F P.numClaims) (SpongeChalTensorMulti P W M bits)
      (P.batches + (k + 1))) :
    spongeDoomedTensorMulti P W M coord bits θ (P.batches + (k + 1)) t ↔
      PcsRbr.grindDoomed bits (PcsRbr.doomedTensorMulti P.ldt P.shift coord θ P.queries) (k + 1)
        (extractPcsTensorMulti P W M bits (k + 1) t) := by
  unfold spongeDoomedTensorMulti
  rw [dite_eq_left (by omega)]
  have hsub : P.batches + (k + 1) - P.batches = k + 1 := Nat.add_sub_cancel_left P.batches (k + 1)
  have hgen : ∀ (n : ℕ) (hn : n = k + 1) (heq : P.batches + n = P.batches + (k + 1)),
      PcsRbr.grindDoomed bits (PcsRbr.doomedTensorMulti P.ldt P.shift coord θ P.queries) n
        (extractPcsTensorMulti P W M bits n (cast (by rw [heq]) t)) ↔
      PcsRbr.grindDoomed bits (PcsRbr.doomedTensorMulti P.ldt P.shift coord θ P.queries) (k + 1)
        (extractPcsTensorMulti P W M bits (k + 1) t) := by
    rintro n rfl heq; rfl
  exact hgen _ hsub (Nat.add_sub_of_le (by omega))

/-- **Round-by-round soundness of the single-root incremental sponge multi-arity
tensor protocol (`entryCap = 1`, `c = 3 / 2`).** -/
theorem rbrSound_spongeTensorMulti (P : MultiParams F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (hinj : ∀ j ≤ P.rounds, Function.Injective (coord j))
    (bits : ℕ → ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) W M θ (εα j))
    (hε₀ : ∀ j ≤ P.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < P.rounds,
      StepMCAArity (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1))
        (P.ldt.degree (i + 1)) θ (εβ i)) :
    RbrSound (P.batches + (P.rounds + 2)) (spongeDoomedTensorMulti P W M coord bits θ)
      (fun i => if i < P.batches then 0
        else roundErrorTensor P.rounds ε₀ εβ θ P.queries (i - P.batches) /
          2 ^ bits (i - P.batches)) := by
  have hrbr := PcsRbr.rbrSound_grind_tensorMulti P.ldt P.shift_ne coord hinj hθ P.queries bits
    hmca hε₀ hstep
  intro i hi t m hdoom
  by_cases hlt : i < P.batches
  · simp only [hlt, ↓reduceIte]
    refine FractionLE.false.mono_left fun c hc => hc ?_
    unfold spongeDoomedTensorMulti
    rw [dite_eq_right (by omega)]
    trivial
  · simp only [hlt, ↓reduceIte]
    have hge : P.batches ≤ i := Nat.le_of_not_lt hlt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    have hk_lt : k < P.rounds + 2 := by omega
    rw [Nat.add_sub_cancel_left]
    have hdoom0 : PcsRbr.grindDoomed bits
        (PcsRbr.doomedTensorMulti P.ldt P.shift coord θ P.queries) k
        (extractPcsTensorMulti P W M bits k t) := by
      cases k with
      | zero =>
        exact PcsRbr.grindDoomed_nil
          (PcsRbr.doomedTensorMulti_zero P.ldt P.shift coord θ P.queries _)
      | succ k' =>
        exact (spongeDoomedTensorMulti_add_succ P W M coord bits θ k' t).mp hdoom
    have hfrac := hrbr k hk_lt (extractPcsTensorMulti P W M bits k t)
      (extractStepPcsMsgMulti P (extractBatchFnMulti P t) k m) hdoom0
    obtain ⟨S, hScard, hSmem⟩ := hfrac
    refine ⟨S.map ⟨spongeChalTensorMultiOf P W M bits, fun a b hab => by
        have := congrArg (spongeChalTensorMultiCast P W M bits) hab
        simpa [spongeChalTensorMultiCast_of] using this⟩, ?_, fun c hc => ?_⟩
    · rw [Finset.card_map]
      have hcardEq : Fintype.card (SpongeChalTensorMulti P W M bits (P.batches + k)) =
          Fintype.card (GrindChal bits (ChalTensorMulti P.ldt W M P.queries) k) :=
        Fintype.card_congr
          { toFun := spongeChalTensorMultiCast P W M bits
            invFun := spongeChalTensorMultiOf P W M bits
            left_inv := spongeChalTensorMultiOf_cast P W M bits
            right_inv := spongeChalTensorMultiCast_of P W M bits }
      rw [hcardEq]
      exact hScard
    · rw [Finset.mem_map]
      refine ⟨spongeChalTensorMultiCast P W M bits c, hSmem _ ?_,
        spongeChalTensorMultiOf_cast P W M bits c⟩
      intro hgood
      apply hc
      exact (spongeDoomedTensorMulti_add_succ P W M coord bits θ k (t.snoc m c)).mpr hgood

end CompiledSpongeMulti

end CertiFri.Compiled
