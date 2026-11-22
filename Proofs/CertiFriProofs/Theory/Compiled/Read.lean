import CertiFriProofs.Poly
import CertiFriProofs.Theory.PcsRbr
import CertiFriProofs.Theory.Oracle.MerkleCommitted

/-!
# The compiled protocol: parameters, messages, and how a message is read

The oracle-model protocol of `Theory/PcsRbr.lean` exchanges functions. In the
compiled protocol the prover sends Merkle roots, evaluation claims and the
coefficients of the final polynomial, and the verifier derives its challenges
from a random oracle. This file fixes the public parameters and the messages of
the compiled protocol, and defines how a message is read, against the rows the
hash queries of a log commit its roots to, as a message of the oracle-model
protocol.

## Parameters

`Params F` holds what is public: a primitive `2 ^ n`-th root of unity `ω`, the
number `rounds` of folding rounds, the bound `finalDegree` on the number of
coefficients of the final polynomial, the coset shift, the number of queries,
and the *shape* of the inputs: the dimensions of the matrices of every input
batch, and for every level `j` the list of claims of that level, each naming a
column of a matrix of a batch (`Slot`). Level `j` is the domain after `j`
folds; a matrix whose columns are claimed at level `j` has log-height `n - j`.
`P.ldt` is the low-degree test on the two-adic domains of `ω`.

## Messages

`Msg F D batches` is one type for all rounds, with a field per kind of content.

* Round `0` reads `inputRoots`, `points` and `values`: one Merkle root per
  input batch, and for every claim its opening point and its claimed value.
* Round `1 + i`, for `i < rounds`, reads `commitRoot`: the root of the
  codeword of level `i`, committed as a matrix of width two and log-height
  `n - i - 1` whose row `p` holds the values at the points of the indices
  `2 * p` and `2 * p + 1` of log-height `n - i`. These two points are
  negations of each other.
* Round `rounds + 1` reads `finalCoeffs`: the coefficients of the final
  polynomial.

A message also has a field `witness`, which no reading looks at. It stands for
Plonky3's proof-of-work witness: it is part of the challenge query of its
round, so a prover can vary it to get another answer of the oracle.

`digestsOf` lists the roots of a message.

## Reading a message

`P.read j msg committed` is the message of `Theory/PcsRbr.lean` that the
message `msg` of round `j` stands for, when `committed root dims m i` is the
row `i` of matrix `m` that `root` commits to (`Oracle.committedRow` of a log).

* The claims (`P.claims`): claim `k` of level `j` is about the function whose
  value at `shift * pointOfIndex ω n (n - j) i` is the entry of the claimed
  column in row `i` of the claimed matrix. The function is zero where no row
  is committed, where the row is too short, and off the coset.
* The word of a folding round (`P.commitWord`): its value at
  `pointOfIndex ω n (n - i) idx` is entry `idx % 2` of row `idx / 2`.
* The final word (`P.finalWord`): the evaluation of the polynomial with the
  first `finalDegree` coefficients of the message. It is a codeword of the last
  level by construction (`isCodeword_finalWord`).

`read_congr` says that the reading depends on `committed` only at the roots in
`digestsOf msg`; this is the hypothesis `hread` of
`Oracle.prob_fsExperiment_bind_committedRow_le`.

## Modelling choices

* Rows are arrays of `F`, for the input matrices and for the committed
  codewords alike. In Plonky3 the input matrices hold base-field elements and
  the codewords extension-field elements; the model has one field.
* The opening points and claimed values are lists indexed by level and by
  claim. A missing entry reads as zero. The executable verifier rejects a proof
  of the wrong shape.
* A final polynomial with more than `finalDegree` coefficients is truncated.
  Plonky3 rejects a final polynomial of any other length than the expected one.
* Every claim has its own opening point. In Plonky3 all columns of a matrix
  share the opening points of the matrix.
* The claims of the levels above `rounds` are not read by the verifier.

Not covered here: the verifier (`Compiled/Verifier.lean`) and the theorems
about it.
-/

namespace CertiFri.Compiled

open Polynomial Oracle

/-! ## Parameters -/

/-- Where a claim points: column `col` of the matrix at position `matrix` of
the input batch `batch`. -/
structure Slot (batches : ℕ) where
  /-- The input batch. -/
  batch : Fin batches
  /-- The position of the matrix in its batch. -/
  matrix : ℕ
  /-- The column of the matrix. -/
  col : ℕ

/-- The public parameters of the compiled protocol.

In Plonky3 terms, with every arity two: `n = log_global_max_height`,
`ω = two_adic_generator(n)`, `rounds = n - (log_blowup + log_final_poly_len)`,
`finalDegree = 2 ^ log_final_poly_len`, `shift = Val::GENERATOR`,
`queries = num_queries`. The batches and their matrices are those of
`commitments_with_opening_points`, with `log_blowup` added to the log-heights;
the claims of level `j` are the pairs of an opening point and a column of the
matrices of log-height `n - j`, in the order `open_inputs` visits them. -/
structure Params (F : Type) [Field F] where
  /-- A primitive `2 ^ n`-th root of unity. -/
  ω : F
  /-- The log of the size of the first domain. -/
  n : ℕ
  /-- The number of folding rounds. -/
  rounds : ℕ
  /-- The final polynomial has degree below `finalDegree`. -/
  finalDegree : ℕ
  /-- The coset shift: the inputs are committed on `shift * H`. -/
  shift : F
  /-- The number of queries. -/
  queries : ℕ
  /-- The number of input batches. Each has one Merkle root. -/
  batches : ℕ
  /-- The dimensions of the matrices of each input batch. -/
  dims : Fin batches → Array Dimensions
  /-- The number of claims of each level. -/
  numClaims : ℕ → ℕ
  /-- The column each claim is about. -/
  slot : ∀ j, Fin (numClaims j) → Slot batches
  /-- `ω` is a primitive `2 ^ n`-th root of unity. -/
  prim : IsPrimitiveRoot ω (2 ^ n)
  /-- The folding rounds do not exhaust the domain. -/
  rounds_le : rounds ≤ n
  /-- The coset shift is not zero. -/
  shift_ne : shift ≠ 0
  /-- No input matrix is taller than the first domain. -/
  height_le : ∀ b, Merkle.maxLogHeight (dims b).toList ≤ n
  /-- A claim of a level `j ≤ rounds` is about a column of a matrix of
  log-height `n - j`. -/
  slot_dims : ∀ j ≤ rounds, ∀ k : Fin (numClaims j), ∃ d : Dimensions,
    (dims (slot j k).batch)[(slot j k).matrix]? = some d ∧ d.logHeight = n - j ∧
      (slot j k).col < d.width

variable {F D : Type}

namespace Params

variable [Field F]

/-- The low-degree test of the protocol: `rounds` folding rounds on the two-adic
domains of `ω`, and a final polynomial of degree below `finalDegree`. -/
def ldt [DecidableEq F] (P : Params F) : LdtInstance F :=
  twoAdicInstance P.ω P.n P.rounds P.finalDegree P.prim P.rounds_le

/-- The number of rounds of `P.ldt`. -/
@[simp] theorem ldt_rounds [DecidableEq F] (P : Params F) : P.ldt.rounds = P.rounds := rfl

/-- The domains of `P.ldt`. -/
@[simp] theorem ldt_domain [DecidableEq F] (P : Params F) (i : ℕ) :
    P.ldt.domain i = twoAdicDomain P.ω P.n i := rfl

/-- The degree bounds of `P.ldt`. -/
@[simp] theorem ldt_degree [DecidableEq F] (P : Params F) (i : ℕ) :
    P.ldt.degree i = 2 ^ (P.rounds - i) * P.finalDegree := rfl

/-- The first domain is not empty. -/
theorem domain_zero_nonempty [DecidableEq F] (P : Params F) : (P.ldt.domain 0).Nonempty :=
  ⟨_, pointOfIndex_mem_twoAdicDomain' P.prim (Nat.zero_le _) 0⟩

/-- The dimensions under which the codeword of level `i` is committed: one
matrix of width two and log-height `n - i - 1`. In `verify_fri` this is
`Dimensions { width: arity, height: 1 << log_folded_height }`. -/
def commitDims (P : Params F) (i : ℕ) : Array Dimensions :=
  #[⟨2, P.n - i - 1⟩]

end Params

/-! ## Messages -/

/-- A prover message of the compiled protocol. Round `0` reads `inputRoots`,
`points` and `values`; round `1 + i` with `i < rounds` reads `commitRoot`;
round `rounds + 1` reads `finalCoeffs`. The other fields of a message are
ignored, and `witness` is ignored in every round. -/
structure Msg (F D : Type) (batches : ℕ) where
  /-- The Merkle root of each input batch. -/
  inputRoots : Fin batches → D
  /-- The opening points of the claims, by level and by claim. -/
  points : List (List F)
  /-- The claimed values, by level and by claim. -/
  values : List (List F)
  /-- The Merkle root of the codeword of a folding round. -/
  commitRoot : D
  /-- The coefficients of the final polynomial, lowest degree first. -/
  finalCoeffs : List F
  /-- The proof-of-work witness. Nothing reads it; it only enters the challenge
  query of the round. -/
  witness : F
  deriving DecidableEq

/-- The opening point of claim `k` of level `j`; zero if the message has none. -/
def Msg.point [Zero F] {batches : ℕ} (msg : Msg F D batches) (j k : ℕ) : F :=
  (msg.points.getD j []).getD k 0

/-- The claimed value of claim `k` of level `j`; zero if the message has none. -/
def Msg.value [Zero F] {batches : ℕ} (msg : Msg F D batches) (j k : ℕ) : F :=
  (msg.values.getD j []).getD k 0

/-- The Merkle roots a message contains at round `j`: `inputRoots` in round `0`,
`commitRoot` in folding rounds `1 .. rounds`, and none in the final round. -/
def digestsOfAt {batches : ℕ} (rounds : ℕ) (j : ℕ) (msg : Msg F D batches) : List D :=
  if j = 0 then List.ofFn msg.inputRoots
  else if j ≤ rounds then [msg.commitRoot]
  else []

/-- The Merkle roots a message contains across all fields. -/
def digestsOf {batches : ℕ} (msg : Msg F D batches) : List D :=
  List.ofFn msg.inputRoots ++ [msg.commitRoot]

/-- The round-`j` digest bound of a message: `batches` at round `0`, `1` at
folding rounds `1 .. rounds`, and `0` after. -/
def digestsBound (batches rounds : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then batches else if j ≤ rounds then 1 else 0

theorem length_digestsOfAt {batches : ℕ} (rounds j : ℕ) (msg : Msg F D batches) :
    (digestsOfAt rounds j msg).length = digestsBound batches rounds j := by
  unfold digestsOfAt digestsBound
  split
  · simp
  · split <;> simp

theorem sum_digestsBound (batches rounds : ℕ) :
    ∑ j ∈ Finset.range (rounds + 2), digestsBound batches rounds j = batches + rounds := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have h0 : digestsBound batches rounds 0 = batches := by simp [digestsBound]
  have hlast : digestsBound batches rounds (rounds + 1) = 0 := by simp [digestsBound]
  have hmid : ∑ k ∈ Finset.range rounds, digestsBound batches rounds (k + 1) = rounds := by
    calc ∑ k ∈ Finset.range rounds, digestsBound batches rounds (k + 1)
        = ∑ _k ∈ Finset.range rounds, 1 := Finset.sum_congr rfl fun k hk => by
          have hk' : k < rounds := Finset.mem_range.mp hk
          simp [digestsBound, Nat.succ_le_of_lt hk']
      _ = rounds := by simp
  omega

/-- Every challenge query brings at most `batches + rounds` digests into play
across the `rounds + 2` rounds. -/
theorem length_chalDigests_le {M : Type} {C : ℕ → Type} {batches : ℕ} (rounds : ℕ)
    (view : M → Msg F D batches) (x : FSQuery M C (HashQuery F D)) :
    (chalDigests (fun j m => digestsOfAt rounds j (view m)) (rounds + 2) x).length ≤
      batches + rounds := by
  unfold chalDigests
  refine (MerkleRO.length_flatMap_zipIdx_le (fun j m => digestsOfAt rounds j (view m))
    (digestsBound batches rounds) (fun j m => (length_digestsOfAt rounds j (view m)).le)
    (x.msgs.take (rounds + 2)) 0).trans ?_
  have hlen : (x.msgs.take (rounds + 2)).length ≤ rounds + 2 := List.length_take_le _ _
  have hsub : Finset.range (x.msgs.take (rounds + 2)).length ⊆ Finset.range (rounds + 2) :=
    Finset.range_mono hlen
  calc ∑ j ∈ Finset.range (x.msgs.take (rounds + 2)).length, digestsBound batches rounds (0 + j)
      = ∑ j ∈ Finset.range (x.msgs.take (rounds + 2)).length, digestsBound batches rounds j := by
        simp
    _ ≤ ∑ j ∈ Finset.range (rounds + 2), digestsBound batches rounds j :=
        Finset.sum_le_sum_of_subset hsub
    _ = batches + rounds := sum_digestsBound batches rounds

/-- A message contains one root per input batch and one more. -/
theorem length_digestsOf {batches : ℕ} (msg : Msg F D batches) :
    (digestsOf msg).length = batches + 1 := by
  rw [digestsOf, List.length_append, List.length_ofFn, List.length_singleton]

/-- The input roots of a message are among its round-`0` roots. -/
theorem inputRoots_mem_digestsOfAt {batches : ℕ} (rounds : ℕ) (msg : Msg F D batches)
    (b : Fin batches) : msg.inputRoots b ∈ digestsOfAt rounds 0 msg := by
  simp [digestsOfAt, List.mem_ofFn]

/-- The root of a folding round is among its round-`j` roots (`1 ≤ j ≤ rounds`). -/
theorem commitRoot_mem_digestsOfAt {batches : ℕ} {rounds j : ℕ} (hj0 : j ≠ 0) (hjr : j ≤ rounds)
    (msg : Msg F D batches) : msg.commitRoot ∈ digestsOfAt rounds j msg := by
  simp [digestsOfAt, hj0, hjr]

/-! ## Functions given by their values at indexed points -/

/-- What a root commits to: `committed root dims m i` is row `i` of matrix `m`
under `root` for matrices of dimensions `dims`, if there is one. The reading of
a log is `Oracle.committedRow`. -/
abbrev Committed (F D : Type) : Type :=
  D → Array Dimensions → ℕ → ℕ → Option (Array F)

variable [Field F]

/-- Entry `col` of a row: zero when there is no row or the row is shorter. -/
def entry (row : Option (Array F)) (col : ℕ) : F :=
  (row.getD #[]).getD col 0

/-- The entries of a row of two values. -/
theorem entry_pair (a b : F) : entry (some #[a, b]) 0 = a ∧ entry (some #[a, b]) 1 = b :=
  ⟨rfl, rfl⟩

variable [DecidableEq F]

/-- The function that takes the value `v i` at the point `g i`, for `i < N`,
and zero at every other point. -/
def ofIndexed (N : ℕ) (g v : ℕ → F) (x : F) : F :=
  if h : ∃ i < N, g i = x then v (Nat.find h) else 0

/-- When `g` is injective on the indices below `N`, the function takes the
value `v i` at `g i`. -/
theorem ofIndexed_apply {N : ℕ} {g : ℕ → F} (hg : ∀ i < N, ∀ j < N, g i = g j → i = j)
    (v : ℕ → F) {i : ℕ} (hi : i < N) : ofIndexed N g v (g i) = v i := by
  have h : ∃ j < N, g j = g i := ⟨i, hi, rfl⟩
  rw [ofIndexed, dite_eq_left h]
  exact congrArg v (hg _ (Nat.find_spec h).1 _ hi (Nat.find_spec h).2)

/-! ## Reading a message -/

namespace Params

variable (P : Params F)

/-- The claims of a message of round `0`, read against committed rows. Claim
`k` of level `j` has the opening point and the claimed value of the message,
and is about the function on the coset of level `j` whose value at
`shift * pointOfIndex ω n (n - j) i` is the entry of the claimed column in
row `i` of the claimed matrix.

In `open_inputs` the opened value `p_at_x` of a column at the query point `x`
is this function at `x`. -/
def claims (msg : Msg F D P.batches) (committed : Committed F D) (j : ℕ)
    (k : Fin (P.numClaims j)) : Claim F where
  f := ofIndexed (2 ^ (P.n - j)) (fun i => P.shift * pointOfIndex P.ω P.n (P.n - j) i) fun i =>
    entry (committed (msg.inputRoots (P.slot j k).batch) (P.dims (P.slot j k).batch)
      (P.slot j k).matrix i) (P.slot j k).col
  z := msg.point j k
  y := msg.value j k

/-- The codeword of level `i`, read from the rows of its commitment: the value
at `pointOfIndex ω n (n - i) idx` is entry `idx % 2` of row `idx / 2`.

In `fold_query` the row of a query at round `i` holds the values of this
function at the query point of level `i` and at its negation. -/
def commitWord (i : ℕ) (rows : ℕ → Option (Array F)) : F → F :=
  ofIndexed (2 ^ (P.n - i)) (pointOfIndex P.ω P.n (P.n - i)) fun idx =>
    entry (rows (idx / 2)) (idx % 2)

/-- The final word: the evaluation of the polynomial with the first
`finalDegree` coefficients of the list. -/
noncomputable def finalWord (coeffs : List F) (x : F) : F :=
  (polyOfCoeffs (coeffs.take P.finalDegree)).eval x

/-- The message of the oracle-model protocol that the message `msg` of round
`j` stands for, given the rows the roots commit to. Round `0` reads only
`claims` (from `inputRoots`), rounds `1 .. rounds` read only `commitWord`
(from `commitRoot`), and rounds past `rounds` read only `finalWord` (no roots). -/
noncomputable def read (j : ℕ) (msg : Msg F D P.batches) (committed : Committed F D) :
    PcsRbr.Msg F P.numClaims where
  claims := if j = 0 then P.claims msg committed else fun _ _ => ⟨fun _ => 0, 0, 0⟩
  word :=
    if j = 0 then fun _ => 0
    else if j ≤ P.rounds then P.commitWord (j - 1) (committed msg.commitRoot (P.commitDims (j - 1)) 0)
    else P.finalWord msg.finalCoeffs

/-- The claims of a message as read in round `0` are `P.claims`. -/
@[simp] theorem read_claims_zero (msg : Msg F D P.batches) (committed : Committed F D) :
    (P.read 0 msg committed).claims = P.claims msg committed := rfl

/-- The word of the message of folding round `i`. -/
theorem read_word_of_lt {i : ℕ} (hi : i < P.rounds) (msg : Msg F D P.batches)
    (committed : Committed F D) :
    (P.read (i + 1) msg committed).word =
      P.commitWord i (committed msg.commitRoot (P.commitDims i) 0) := by
  simp only [read, Nat.succ_ne_zero, ↓reduceIte, ite_eq_left (Nat.succ_le_of_lt hi),
    Nat.add_sub_cancel]

/-- The word of the last message is the final word. -/
theorem read_word_last (msg : Msg F D P.batches) (committed : Committed F D) :
    (P.read (P.rounds + 1) msg committed).word = P.finalWord msg.finalCoeffs := by
  simp only [read, Nat.succ_ne_zero, ↓reduceIte, ite_eq_right (Nat.not_succ_le_self _)]

/-- **The reading of round `j` looks only at the roots of round `j`.** Two
families of committed rows that agree at the roots in `digestsOfAt P.rounds j msg`
give the same reading of `msg` in round `j`. -/
theorem read_congr (j : ℕ) (msg : Msg F D P.batches) (c c' : Committed F D)
    (h : ∀ root ∈ digestsOfAt P.rounds j msg, c root = c' root) :
    P.read j msg c = P.read j msg c' := by
  by_cases hj0 : j = 0
  · subst hj0
    have hin : ∀ b, c (msg.inputRoots b) = c' (msg.inputRoots b) := fun b =>
      h _ (inputRoots_mem_digestsOfAt P.rounds msg b)
    have hclaims : P.claims msg c = P.claims msg c' := by
      funext l k
      simp only [claims, hin]
    simp only [read, ↓reduceIte, hclaims]
  · by_cases hjr : j ≤ P.rounds
    · have hcommit : c msg.commitRoot = c' msg.commitRoot :=
        h _ (commitRoot_mem_digestsOfAt hj0 hjr msg)
      simp only [read, hj0, ↓reduceIte, hjr, hcommit]
    · simp only [read, hj0, ↓reduceIte, hjr]

/-- The function of a claim, at the coset point of the index `i`: the entry of
the claimed column in row `i` of the claimed matrix. -/
theorem claims_f_apply (msg : Msg F D P.batches) (committed : Committed F D) {j : ℕ}
    (k : Fin (P.numClaims j)) {i : ℕ} (hi : i < 2 ^ (P.n - j)) :
    (P.claims msg committed j k).f (P.shift * pointOfIndex P.ω P.n (P.n - j) i) =
      entry (committed (msg.inputRoots (P.slot j k).batch) (P.dims (P.slot j k).batch)
        (P.slot j k).matrix i) (P.slot j k).col :=
  ofIndexed_apply (g := fun i => P.shift * pointOfIndex P.ω P.n (P.n - j) i)
    (fun _ ha _ hb hab =>
      (pointOfIndex_inj P.prim (Nat.sub_le _ _) ha hb).mp (mul_left_cancel₀ P.shift_ne hab))
    (fun i => entry (committed (msg.inputRoots (P.slot j k).batch) (P.dims (P.slot j k).batch)
      (P.slot j k).matrix i) (P.slot j k).col) hi

/-- The codeword of level `i`, at the point of the index `idx`: entry `idx % 2`
of row `idx / 2`. -/
theorem commitWord_apply (i : ℕ) (rows : ℕ → Option (Array F)) {idx : ℕ}
    (hidx : idx < 2 ^ (P.n - i)) :
    P.commitWord i rows (pointOfIndex P.ω P.n (P.n - i) idx) = entry (rows (idx / 2)) (idx % 2) :=
  ofIndexed_apply
    (fun _ ha _ hb hab => (pointOfIndex_inj P.prim (Nat.sub_le _ _) ha hb).mp hab) _ hidx

/-- The final word is a codeword of the last level, whatever the message. -/
theorem isCodeword_finalWord (coeffs : List F) :
    IsCodeword (P.ldt.domain P.ldt.rounds) (P.ldt.degree P.ldt.rounds) (P.finalWord coeffs) := by
  refine ⟨polyOfCoeffs (coeffs.take P.finalDegree), ?_, fun x _ => rfl⟩
  have hlen : (coeffs.take P.finalDegree).length ≤ P.finalDegree := List.length_take_le _ _
  rw [ldt_degree, ldt_rounds, Nat.sub_self, pow_zero, one_mul]
  exact (degree_polyOfCoeffs_lt _).trans_le (by exact_mod_cast hlen)

end Params

/-! ## The messages of a transcript -/

section Transcript

variable {M : Type} {C : ℕ → Type}

/-- The message of round `j` of a transcript with at least one round. For a `j`
beyond the transcript it is the last message. -/
def msgAt : {i : ℕ} → Transcript M C (i + 1) → ℕ → M
  | _, .snoc t m _, j => t.msgs.getD j m

/-- `msgAt` returns the messages of the transcript. -/
theorem getElem?_msgs {i : ℕ} (t : Transcript M C (i + 1)) {j : ℕ} (hj : j ≤ i) :
    t.msgs[j]? = some (msgAt t j) := by
  cases t with
  | snoc t m c =>
    rw [msgAt, Transcript.msgs_snoc, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge j i with hlt | hge
    · have hlen : j < t.msgs.length := by rw [t.length_msgs]; exact hlt
      rw [List.getElem?_append_left hlen, List.getElem?_eq_getElem hlen, Option.getD_some]
    · obtain rfl : j = i := le_antisymm hj hge
      have hlast := List.getElem?_concat_length (l := t.msgs) (a := m)
      rw [t.length_msgs] at hlast
      rw [hlast, List.getElem?_eq_none (by rw [t.length_msgs]), Option.getD_none]

/-- A message the transcript holds at round `j` is `msgAt` of that round. -/
theorem msgAt_eq_of_getElem? {i : ℕ} {t : Transcript M C (i + 1)} {j : ℕ} {m : M}
    (h : t.msgs[j]? = some m) : msgAt t j = m := by
  have hj : j ≤ i := by
    have := (List.getElem?_eq_some_iff.mp h).1
    rw [t.length_msgs] at this
    exact Nat.lt_succ_iff.mp this
  exact Option.some.inj ((getElem?_msgs t hj).symm.trans h)

end Transcript

end CertiFri.Compiled
