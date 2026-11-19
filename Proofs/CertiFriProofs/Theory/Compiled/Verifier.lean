import CertiFriProofs.Theory.Compiled.Read
import CertiFriProofs.Theory.PcsRbr.Grinding
import CertiFriProofs.Theory.Oracle.MerkleAccept

/-!
# The compiled protocol: the model verifier

The verifier of the compiled protocol, as a computation that queries the random
oracle for every hash evaluation. It follows Plonky3's `verify_fri`
(`fri/src/verifier.rs`) for arity two, after the challenges are derived:

1. `open_inputs`, first half. For each input batch, the Merkle check of the
   opened rows of all queries against the root of the batch
   (`verifyOpeningsM`, which is `verify_multi_batch`). The index of a query is
   shifted to the tallest matrix of the batch.
2. `open_inputs`, second half, and `fold_query`. For each query, the reduced
   opening of every level from the opened values (`Params.reduced`), then the
   fold chain (`Params.foldChain`): the row of a round holds the value folded
   so far and the sibling value from the proof, placed by the low bit of the
   index (`placeRow`); the row is folded with `fold_row` (`foldRow`) and the
   reduced opening of the next level is added with the factor `β ^ 2`. After
   the last round the value is compared with the final polynomial at the point
   the query has reached.
3. For each folding round, the Merkle check of the rows of all queries, as
   reconstructed in step 2, against the root of the round.

`Params.verifyWith` is the verifier on the values it reads off a transcript:
the messages, `α`, the folding challenges and the query indices. It only makes
hash queries, so it runs against an oracle with any challenge types and any
type of messages in its challenge queries: it serves the protocol with and
without proof of work, and a transcript whose messages are of another type
than `Msg`.

* `Params.verify` is the verifier on a transcript of the protocol without
  proof of work.
* `Params.verifyGrind` is the verifier on a transcript with proof-of-work
  samples: it rejects unless every sample is zero (`check_witness`), and then
  runs the same checks.
* `Params.verifyGrindView` is `verifyGrind` on a transcript of raw messages of
  any type `M`, each read as a `Msg` through a function `view`. The challenge
  queries of the oracle then carry the raw messages. `verifyGrind` is the case
  `view := id` (`Params.verifyGrind_eq_verifyGrindView`).
* `Params.queryBound_verifyWith`: the verifier makes at most
  `P.verifierQueries = (batches + rounds) * (queries * (3 * n + 1))` queries.
* `Params.run_verifyWith`: against a total answer function `f`, the verifier
  returns the conjunction of the executable Merkle checks
  (`Merkle.verifyOpenings` for the hasher `hasherOf f`) and of the comparison
  with the final polynomial.
* `Params.run_verifyGrindView`: against `f`, the verifier with proof of work
  accepts exactly when every sample is zero and `verifyWith` accepts.

## Query indices

In the oracle-model protocol the challenge of the query round is a tuple of
points of the first domain. The verifier works with indices: `P.indexOf x` is
the index below `2 ^ n` whose point is `x`. `pointOfIndex ω n n` is a bijection
from these indices onto the first domain (`bijOn_pointOfIndex`), so a uniform
point is the point of a uniform index.

## What the model verifier does not check

Plonky3's verifier rejects in more cases than this one. The soundness proof
does not need these checks, so the model leaves them out:

* the shape checks on the proof (numbers of openings, of sibling values, of
  proof-of-work witnesses, the length of the final polynomial, the agreement of
  the two derivations of `log_global_max_height`): here the proof data is typed
  by query and by round, and a missing value reads as zero;
* `OpeningPointMatchesQueryPoint`, the rejection of a query whose point is an
  opening point: here the quotient is zero there (division by zero);
* the check that the reduced opening at height `log_blowup` is zero;
* inputs at heights the fold never reaches, and a missing input at the first
  height: here the claims of levels above `rounds` are ignored, and a level
  without claims has the reduced opening zero;
* the rejection of an instance with no queries.

Not covered: folding with arity above two, and extra query index bits
(`extra_query_index_bits` is zero for `TwoAdicFriPcs`). The proof-of-work
witness is not an input of the verifier: it is a field of the prover message
that only enters the challenge query (`Compiled/Read.lean`).
-/

namespace CertiFri.Compiled

open Polynomial Oracle OracleComp MerkleRO
open PcsRbr (Chal alphaOf betasOf queriesOf GrindChal PowPasses ungrind)

variable {F D : Type}

/-! ## Proof data -/

/-- What a proof holds beside the messages: for each query, the opened rows of
the input batches and the sibling values of the folding rounds, each with a
Merkle path. In Plonky3 these are `input_openings` and `commit_phase_openings`;
there one proof authenticates all queries of a batch or of a round, here each
query has its own path. -/
structure Proof (F D : Type) (batches queries : ℕ) where
  /-- The opened rows of the matrices of an input batch, at a query. -/
  inputRows : Fin batches → Fin queries → Array (Array F)
  /-- The Merkle path of the opened rows of an input batch, at a query. -/
  inputPaths : Fin batches → Fin queries → List D
  /-- The sibling value of a folding round, at a query. -/
  siblings : ℕ → Fin queries → F
  /-- The Merkle path of the row of a folding round, at a query. -/
  commitPaths : ℕ → Fin queries → List D

/-! ## The arithmetic of one query -/

section Arithmetic

variable [Field F]

/-- Plonky3's `fold_row` for arity two: the value at `β` of the line through
`(x, e₀)` and `(-x, e₁)`. -/
def foldRow (β x e₀ e₁ : F) : F :=
  e₀ + (β - x) * (e₁ - e₀) / (-x - x)

/-- The evaluation of a coefficient list by Horner's rule, as `verify_fri`
evaluates the final polynomial. -/
def hornerEval (coeffs : List F) (x : F) : F :=
  coeffs.foldr (fun c acc => acc * x + c) 0

/-- Horner's rule computes the evaluation of the polynomial. -/
theorem hornerEval_eq_eval (coeffs : List F) (x : F) :
    hornerEval coeffs x = (polyOfCoeffs coeffs).eval x :=
  (eval_polyOfCoeffs x coeffs).symm

/-- The row of a folding round: the value folded so far and the sibling value,
placed by the low bit of the index. In `fold_query` this is `evals`, with
`index_in_group = start_index % arity`. -/
def placeRow (folded sibling : F) (index : ℕ) : F × F :=
  if index % 2 = 0 then (folded, sibling) else (sibling, folded)

namespace Params

variable (P : Params F)

/-- The opened value of claim `k` of level `j` at the query `t`: the entry of
the claimed column in the opened row of the claimed matrix. In `open_inputs`
this is `p_at_x`. -/
def opened (pf : Proof F D P.batches P.queries) (t : Fin P.queries) (j : ℕ)
    (k : Fin (P.numClaims j)) : F :=
  entry ((pf.inputRows (P.slot j k).batch t)[(P.slot j k).matrix]?) (P.slot j k).col

/-- The reduced opening of level `j` at the query index `index`, from the
opened values: claim `k` enters with `α ^ k`, as the quotient
`(y - value) / (z - shift * x)` at the point `x` of the index at log-height
`n - j`. In `open_inputs` this is the entry of `reduced_openings` for
`log_height = n - j`. -/
def reduced (msg : Msg F D P.batches) (opened : ∀ j, Fin (P.numClaims j) → F) (α : F)
    (index j : ℕ) : F :=
  ∑ k : Fin (P.numClaims j), α ^ (k : ℕ) * ((msg.value j k - opened j k) /
    (msg.point j k - P.shift * pointOfIndex P.ω P.n (P.n - j) (index >>> j)))

/-- The fold chain of `fold_query`: the value after `i` folding rounds. It
starts with the reduced opening of level `0`. In round `i` the row holds the
value so far and the sibling value `sib i`, placed by the low bit of
`index >>> i`; the row is folded with `β i` at the point of its first entry,
and `β i ^ 2` times the reduced opening of level `i + 1` is added. -/
def foldChain (ro sib β : ℕ → F) (index : ℕ) : ℕ → F
  | 0 => ro 0
  | i + 1 =>
    foldRow (β i) (pointOfIndex P.ω P.n (P.n - i) (2 * (index >>> (i + 1))))
        (placeRow (foldChain ro sib β index i) (sib i) (index >>> i)).1
        (placeRow (foldChain ro sib β index i) (sib i) (index >>> i)).2 +
      β i ^ 2 * ro (i + 1)

/-- The value of the fold chain of the query `t` after `i` rounds, from the
proof, the message of round `0` and the challenges. -/
def folded (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches) (α : F) (β : ℕ → F)
    (index : ℕ) (t : Fin P.queries) (i : ℕ) : F :=
  P.foldChain (P.reduced msg₀ (P.opened pf t) α index) (fun i => pf.siblings i t) β index i

/-- The row of the query `t` at the folding round `i`, as the verifier
reconstructs it: the value folded so far and the sibling value of the proof. -/
def commitRow (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches) (α : F)
    (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) : F × F :=
  placeRow (P.folded pf msg₀ α β index t i) (pf.siblings i t) (index >>> i)

/-- The fold chain starts with the reduced opening of level `0`. -/
theorem folded_zero (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches) (α : F)
    (β : ℕ → F) (index : ℕ) (t : Fin P.queries) :
    P.folded pf msg₀ α β index t 0 = P.reduced msg₀ (P.opened pf t) α index 0 := rfl

/-- One round of the fold chain: fold the row, add the next reduced opening. -/
theorem folded_succ (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches) (α : F)
    (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) :
    P.folded pf msg₀ α β index t (i + 1) =
      foldRow (β i) (pointOfIndex P.ω P.n (P.n - i) (2 * (index >>> (i + 1))))
          (P.commitRow pf msg₀ α β index t i).1 (P.commitRow pf msg₀ α β index t i).2 +
        β i ^ 2 * P.reduced msg₀ (P.opened pf t) α index (i + 1) := rfl

end Params

end Arithmetic

/-! ## The verifier -/

variable [Field F] [DecidableEq F] [DecidableEq D]

namespace Params

variable (P : Params F)

/-- The Merkle checks of the input batches: for each batch, the opened rows of
all queries against the root of the batch in the message of round `0`. The
index of a query is shifted to the tallest matrix of the batch, as
`reduced_indices` in `open_inputs`. -/
def inputChecks {M : Type} {C : ℕ → Type} (pf : Proof F D P.batches P.queries)
    (msg₀ : Msg F D P.batches) (index : Fin P.queries → ℕ) :
    List (OracleComp (MerkleAnswer M C F D) Bool) :=
  (List.finRange P.batches).map fun b =>
    verifyOpeningsM (msg₀.inputRoots b) (P.dims b)
      (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
      (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))

/-- The Merkle checks of the folding rounds: for each round `i`, the rows of
all queries, as reconstructed by the fold chain, against the root in the
message of round `1 + i`. The row of a query is at its index shifted by
`i + 1`. In `verify_fri` these are `rows_by_round` and `group_indices_by_round`. -/
def commitChecks {M : Type} {C : ℕ → Type} (pf : Proof F D P.batches P.queries)
    (msg : ℕ → Msg F D P.batches) (α : F) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    List (OracleComp (MerkleAnswer M C F D) Bool) :=
  (List.range P.rounds).map fun i =>
    verifyOpeningsM (msg (i + 1)).commitRoot (P.commitDims i)
      (Array.ofFn fun t => index t >>> (i + 1))
      (Array.ofFn fun t => #[#[(P.commitRow pf (msg 0) α β (index t) t i).1,
        (P.commitRow pf (msg 0) α β (index t) t i).2]])
      (Array.ofFn (pf.commitPaths i))

/-- The comparison with the final polynomial: for every query, the value of
the fold chain after all rounds is the value of the final polynomial, with the
first `finalDegree` coefficients of the message of round `rounds + 1`, at the
point of the query index shifted by `rounds`. `verify_fri` writes this point as
`two_adic_generator(n) ^ reverse_bits_len(domain_index, n)`, which is the same
(`finalPoint_eq_pointOfIndex`). -/
def FinalCheck (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches) (α : F)
    (β : ℕ → F) (index : Fin P.queries → ℕ) : Prop :=
  ∀ t, P.folded pf (msg 0) α β (index t) t P.rounds =
    hornerEval ((msg (P.rounds + 1)).finalCoeffs.take P.finalDegree)
      (pointOfIndex P.ω P.n (P.n - P.rounds) (index t >>> P.rounds))

/-- The comparison with the final polynomial is decidable. -/
instance (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches) (α : F) (β : ℕ → F)
    (index : Fin P.queries → ℕ) : Decidable (P.FinalCheck pf msg α β index) := by
  unfold FinalCheck
  infer_instance

/-- **The model verifier**, on the values it reads off a transcript: `msg j` is
the prover message of round `j`, `α` the batching challenge, `β i` the folding
challenge of round `i`, and `index t` the index of the query `t`. It runs the
Merkle checks of the input batches, compares every fold chain with the final
polynomial, and runs the Merkle checks of the folding rounds; it accepts when
all of them pass. Every hash evaluation is a query to the oracle. It makes no
challenge query, so the oracle may have any type `M` of messages and any
challenge types `C` in its challenge queries. -/
def verifyWith {M : Type} {C : ℕ → Type} (pf : Proof F D P.batches P.queries)
    (msg : ℕ → Msg F D P.batches) (α : F) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    OracleComp (MerkleAnswer M C F D) Bool :=
  (allM (P.inputChecks pf (msg 0) index)).bind fun ok =>
    if ok && decide (P.FinalCheck pf msg α β index) then allM (P.commitChecks pf msg α β index)
    else .pure false

/-- The number of oracle queries the verifier makes at most: a Merkle check
per input batch and per folding round, each with at most `3 * n + 1` queries
per query index. -/
def verifierQueries : ℕ :=
  (P.batches + P.rounds) * (P.queries * (3 * P.n + 1))

/-- **Query bound of the verifier.** -/
theorem queryBound_verifyWith {M : Type} {C : ℕ → Type} (pf : Proof F D P.batches P.queries)
    (msg : ℕ → Msg F D P.batches) (α : F) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    (P.verifyWith (M := M) (C := C) pf msg α β index).QueryBound P.verifierQueries := by
  have hin : (allM (P.inputChecks (M := M) (C := C) pf (msg 0) index)).QueryBound
      (P.batches * (P.queries * (3 * P.n + 1))) := by
    have h := queryBound_allM (n := P.queries * (3 * P.n + 1))
      (P.inputChecks (M := M) (C := C) pf (msg 0) index) fun c hc => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
        refine (queryBound_verifyOpeningsM _ _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        exact Nat.mul_le_mul_left _ (by have := P.height_le b; omega)
    rwa [inputChecks, List.length_map, List.length_finRange] at h
  have hcommit : (allM (P.commitChecks (M := M) (C := C) pf msg α β index)).QueryBound
      (P.rounds * (P.queries * (3 * P.n + 1))) := by
    have h := queryBound_allM (n := P.queries * (3 * P.n + 1))
      (P.commitChecks (M := M) (C := C) pf msg α β index) fun c hc => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
        refine (queryBound_verifyOpeningsM _ _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        refine Nat.mul_le_mul_left _ ?_
        have : Merkle.maxLogHeight (P.commitDims i).toList ≤ P.n := by
          simp only [commitDims, List.toList_toArray, Merkle.maxLogHeight]
          omega
        omega
    rwa [commitChecks, List.length_map, List.length_range] at h
  refine QueryBound.mono (hin.bind fun ok => ?_) (by rw [verifierQueries, Nat.add_mul])
  split
  · exact hcommit
  · exact queryBound_pure _ _

/-- **The verifier against a fixed hash function.** Against a total answer
function `f`, the verifier returns the conjunction of the executable Merkle
checks of the input batches, of the comparison with the final polynomial, and
of the executable Merkle checks of the folding rounds, for the hasher
`hasherOf f`. -/
theorem run_verifyWith {M : Type} {C : ℕ → Type}
    (f : ∀ x : FSQuery M C (HashQuery F D), MerkleAnswer M C F D x)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches) (α : F) (β : ℕ → F)
    (index : Fin P.queries → ℕ) :
    (P.verifyWith pf msg α β index).run f =
      (((List.finRange P.batches).all fun b =>
          Merkle.verifyOpenings (hasherOf f) ((msg 0).inputRoots b) (P.dims b)
            (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
            (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))) &&
        decide (P.FinalCheck pf msg α β index) &&
        (List.range P.rounds).all fun i =>
          Merkle.verifyOpenings (hasherOf f) (msg (i + 1)).commitRoot (P.commitDims i)
            (Array.ofFn fun t => index t >>> (i + 1))
            (Array.ofFn fun t => #[#[(P.commitRow pf (msg 0) α β (index t) t i).1,
              (P.commitRow pf (msg 0) α β (index t) t i).2]])
            (Array.ofFn (pf.commitPaths i))) := by
  rw [verifyWith, run_bind, run_allM, inputChecks, List.all_map]
  simp only [Function.comp_def, run_verifyOpeningsM]
  split
  · next h =>
    rw [run_allM, commitChecks, List.all_map]
    simp only [Function.comp_def, run_verifyOpeningsM]
    rw [h, Bool.true_and]
  · next h =>
    rw [run_pure, (Bool.not_eq_true _).mp h, Bool.false_and]

/-! ## Query indices -/

/-- The index below `2 ^ n` of a point of the first domain; zero for a point
outside it. -/
def indexOf (x : F) : ℕ :=
  if h : ∃ index < 2 ^ P.n, pointOfIndex P.ω P.n P.n index = x then Nat.find h else 0

/-- An index of a point is below `2 ^ n`. -/
theorem indexOf_lt (x : F) : P.indexOf x < 2 ^ P.n := by
  unfold indexOf
  split
  · next h => exact (Nat.find_spec h).1
  · exact Nat.two_pow_pos _

/-- The point of the index of a point of the first domain is that point. -/
theorem pointOfIndex_indexOf {x : F} (hx : x ∈ twoAdicDomain P.ω P.n 0) :
    pointOfIndex P.ω P.n P.n (P.indexOf x) = x := by
  have h : ∃ index < 2 ^ P.n, pointOfIndex P.ω P.n P.n index = x :=
    exists_pointOfIndex_eq P.prim le_rfl (by rwa [Nat.sub_self])
  rw [indexOf, dite_eq_left h]
  exact (Nat.find_spec h).2

/-- The index of the point of an index below `2 ^ n` is that index. -/
theorem indexOf_pointOfIndex {index : ℕ} (hindex : index < 2 ^ P.n) :
    P.indexOf (pointOfIndex P.ω P.n P.n index) = index :=
  (pointOfIndex_inj P.prim le_rfl (P.indexOf_lt _) hindex).mp
    (P.pointOfIndex_indexOf (by
      simpa using pointOfIndex_mem_twoAdicDomain P.prim P.n index))

/-! ## The verifier on a transcript -/

/-- **The model verifier of the protocol without proof of work.** It reads the
messages and the challenges off the transcript, takes the indices of the query
points, and runs `verifyWith`. -/
def verify (pf : Proof F D P.batches P.queries)
    (t : Transcript (Msg F D P.batches) (Chal P.ldt P.queries) (P.rounds + 2)) :
    OracleComp (MerkleAnswer (Msg F D P.batches) (Chal P.ldt P.queries) F D) Bool :=
  P.verifyWith pf (msgAt t) (alphaOf t) (betasOf t) fun k => P.indexOf (queriesOf t k)

/-- Whether every proof-of-work sample of a transcript is zero is decidable. -/
instance decidablePowPasses {M : Type} {C : ℕ → Type} {bits : ℕ → ℕ} :
    ∀ {i : ℕ} (t : Transcript M (GrindChal bits C) i), Decidable (PowPasses t)
  | _, .nil => isTrue trivial
  | _, .snoc t _ c =>
    haveI := decidablePowPasses t
    inferInstanceAs (Decidable (PowPasses t ∧ (c.1 : ℕ) = 0))

/-- **The model verifier of the protocol with proof of work.** The challenge of
round `i` comes with a proof-of-work sample of `bits i` bits. The verifier
rejects unless every sample is zero (Plonky3's `check_witness`), and then runs
the checks of `verifyWith` on the transcript without the samples. -/
def verifyGrind (bits : ℕ → ℕ) (pf : Proof F D P.batches P.queries)
    (t : Transcript (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)) :
    OracleComp (MerkleAnswer (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) F D)
      Bool :=
  if PowPasses t then
    P.verifyWith pf (msgAt (ungrind t)) (alphaOf (ungrind t)) (betasOf (ungrind t)) fun k =>
      P.indexOf (queriesOf (ungrind t) k)
  else .pure false

/-- **The model verifier with proof of work, on raw messages.** The messages of
the transcript, and of the challenge queries of the oracle, are of a type `M`,
and `view` reads such a message as a message of the model. The verifier rejects
unless every proof-of-work sample is zero, and then runs the checks of
`verifyWith` on the messages read through `view` and on the challenges of the
transcript without the samples. -/
def verifyGrindView {M : Type} (bits : ℕ → ℕ) (view : M → Msg F D P.batches)
    (pf : Proof F D P.batches P.queries)
    (t : Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)) :
    OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) Bool :=
  if PowPasses t then
    P.verifyWith pf (fun j => view (msgAt (ungrind t) j)) (alphaOf (ungrind t))
      (betasOf (ungrind t)) fun k => P.indexOf (queriesOf (ungrind t) k)
  else .pure false

/-- The verifier with proof of work is the verifier on raw messages for the
messages of the model read as they are. -/
theorem verifyGrind_eq_verifyGrindView (bits : ℕ → ℕ) (pf : Proof F D P.batches P.queries)
    (t : Transcript (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)) :
    P.verifyGrind bits pf t = P.verifyGrindView bits id pf t := rfl

/-- The verifier without proof of work makes at most `P.verifierQueries` queries. -/
theorem queryBound_verify (pf : Proof F D P.batches P.queries)
    (t : Transcript (Msg F D P.batches) (Chal P.ldt P.queries) (P.rounds + 2)) :
    (P.verify pf t).QueryBound P.verifierQueries :=
  P.queryBound_verifyWith pf _ _ _ _

/-- The verifier with proof of work makes at most `P.verifierQueries` queries. -/
theorem queryBound_verifyGrind (bits : ℕ → ℕ) (pf : Proof F D P.batches P.queries)
    (t : Transcript (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)) :
    (P.verifyGrind bits pf t).QueryBound P.verifierQueries := by
  unfold verifyGrind
  split
  · exact P.queryBound_verifyWith pf _ _ _ _
  · exact queryBound_pure _ _

/-- **The verifier with proof of work against a fixed hash function.** Against
a total answer function `f`, the verifier on raw messages accepts exactly when
every proof-of-work sample of the transcript is zero and `verifyWith` accepts
against `f` (see `run_verifyWith`). -/
theorem run_verifyGrindView {M : Type} (bits : ℕ → ℕ) (view : M → Msg F D P.batches)
    (f : ∀ x : FSQuery M (GrindChal bits (Chal P.ldt P.queries)) (HashQuery F D),
      MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D x)
    (pf : Proof F D P.batches P.queries)
    (t : Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)) :
    (P.verifyGrindView bits view pf t).run f = true ↔
      PowPasses t ∧
        (P.verifyWith pf (fun j => view (msgAt (ungrind t) j)) (alphaOf (ungrind t))
          (betasOf (ungrind t)) fun k => P.indexOf (queriesOf (ungrind t) k)).run f = true := by
  unfold verifyGrindView
  split
  · next h => exact (and_iff_right h).symm
  · next h =>
    rw [run_pure]
    exact ⟨fun h' => absurd h' (by simp), fun h' => absurd h'.1 h⟩

/-- The verifier with proof of work on raw messages makes at most
`P.verifierQueries` queries. -/
theorem queryBound_verifyGrindView {M : Type} (bits : ℕ → ℕ) (view : M → Msg F D P.batches)
    (pf : Proof F D P.batches P.queries)
    (t : Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)) :
    (P.verifyGrindView bits view pf t).QueryBound P.verifierQueries := by
  unfold verifyGrindView
  split
  · exact P.queryBound_verifyWith pf _ _ _ _
  · exact queryBound_pure _ _

end Params

end CertiFri.Compiled
