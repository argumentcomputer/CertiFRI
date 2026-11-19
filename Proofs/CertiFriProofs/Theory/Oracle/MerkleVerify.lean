import CertiFri.Merkle
import CertiFriProofs.Theory.Oracle.FiatShamir

/-!
# The Merkle check as an oracle computation

The two hash functions of a Merkle tree, modelled as one random oracle, and the
verifier's check of an opening as a computation that queries it.

* `HashQuery T D` is a query to one of the two hash functions: the hash of the
  entries of a leaf or of an injection (`rows`), or the compression of two
  digests (`node`). Every answer is a digest in `D`.
* The hash queries are the queries of the second kind of the Fiat–Shamir
  experiment: the oracle is `MerkleAnswer Msg Chal T D`, for any types of prover
  messages and challenges.
* `hasherOf f` is the hasher a total answer function `f` defines.
* `verifyOpeningM` and `verifyOpeningsM` are the checks `Merkle.verifyOpening`
  and `Merkle.verifyOpenings` with every hash evaluation made as a query. The
  shape of an opening is checked first, and no query is made if it is wrong.

## Results

* `run_verifyOpeningM`, `run_verifyOpeningsM`: against a total answer function
  `f`, the computations return what the executable checks return for the hasher
  `hasherOf f`. `run_verifyOpeningsM_eq_verifyMultiBatch` states the second for
  the commitment scheme `merkleMmcs (hasherOf f)`.
* `queryBound_verifyOpeningM`, `queryBound_verifyOpeningsM`: an opening at one
  index takes at most `3 * maxLogHeight dims + 1` queries: one for the leaf,
  and for each level one compression with the sibling and at most two queries
  for an injection.

There are no assumptions. The tree is the one of `CertiFri/Merkle.lean`: a
two-to-one compression, power-of-two heights, a single root.

Not covered: the two hash functions as independent oracles with different
answer types (both answer in `D`, and a `rows` query and a `node` query are
different queries of the one oracle); the number of queries as a function of
the heights that occur (the bound charges an injection at every level).
-/

namespace CertiFri.Oracle

universe u v w

/-- A query to one of the two hash functions of a Merkle tree over entries `T`
and digests `D`. -/
inductive HashQuery (T D : Type) : Type
  /-- The hash of the entries of a leaf or of an injection. -/
  | rows (xs : Array T) : HashQuery T D
  /-- The compression of two digests. -/
  | node (a b : D) : HashQuery T D
  deriving DecidableEq

/-- The answer types of the oracle that answers the challenge queries of a
Fiat–Shamir experiment and the hash queries of a Merkle tree: a challenge query
of round `i` is answered in `Chal i`, a hash query in `D`. -/
abbrev MerkleAnswer (Msg : Type u) (Chal : ℕ → Type) (T D : Type) :
    FSQuery Msg Chal (HashQuery T D) → Type :=
  FSAnswer (Msg := Msg) Chal fun _ : HashQuery T D => D

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

/-- The hasher a total answer function defines: its two functions are the
answers to the `rows` and to the `node` queries. -/
def hasherOf (f : ∀ x : FSQuery Msg Chal (HashQuery T D), MerkleAnswer Msg Chal T D x) :
    MerkleHasher T D where
  hashRows xs := f (.other (.rows xs))
  compress a b := f (.other (.node a b))

open OracleComp Merkle

/-! ## The steps of the climb, as queries -/

namespace MerkleRO

/-- Query the hash of the entries `xs`. -/
def hashRowsM (xs : Array T) : OracleComp (MerkleAnswer Msg Chal T D) D :=
  query (X := FSQuery Msg Chal (HashQuery T D)) (.other (.rows xs))

/-- Query the compression of `a` and `b`. -/
def compressM (a b : D) : OracleComp (MerkleAnswer Msg Chal T D) D :=
  query (X := FSQuery Msg Chal (HashQuery T D)) (.other (.node a b))

/-- `Merkle.groupDigest` with the hash as a query. -/
def groupDigestM (dims : List Dimensions) (rows : List (Array T)) (h : ℕ) :
    OracleComp (MerkleAnswer Msg Chal T D) D :=
  hashRowsM (groupRows dims rows h).toArray

/-- `Merkle.inject` with the hash and the compression as queries. -/
def injectM (dims : List Dimensions) (rows : List (Array T)) (h : ℕ) (digest : D) :
    OracleComp (MerkleAnswer Msg Chal T D) D :=
  if hasHeight dims h then (groupDigestM dims rows h).bind fun group => compressM digest group
  else .pure digest

/-- `Merkle.parent` with the compression as a query. -/
def parentM (index : ℕ) (digest sibling : D) : OracleComp (MerkleAnswer Msg Chal T D) D :=
  if index % 2 = 0 then compressM digest sibling else compressM sibling digest

/-- `Merkle.climb` with every hash evaluation as a query. -/
def climbM (dims : List Dimensions) (rows : List (Array T)) :
    (h index : ℕ) → (digest : D) → (path : List D) → OracleComp (MerkleAnswer Msg Chal T D) D
  | _, _, digest, [] => .pure digest
  | h, index, digest, sibling :: path =>
    (parentM index digest sibling).bind fun node =>
      (injectM dims rows (h - 1) node).bind fun digest' =>
        climbM dims rows (h - 1) (index / 2) digest' path

/-- Run the computations of a list in order, until one returns `false`. The
result is whether all returned `true`. -/
def allM {X : Type v} {Y : X → Type w} : List (OracleComp Y Bool) → OracleComp Y Bool
  | [] => .pure true
  | c :: cs => c.bind fun b => if b then allM cs else .pure false

end MerkleRO

open MerkleRO

/-! ## The checks -/

/-- `Merkle.verifyOpening` as an oracle computation: check the shape of the
opening, then climb from the leaf to the root with one query per hash
evaluation, and compare with `root`. No query is made if the shape is wrong. -/
def verifyOpeningM [DecidableEq D] (root : D) (dims : Array Dimensions) (index : ℕ)
    (rows : Array (Array T)) (path : List D) : OracleComp (MerkleAnswer Msg Chal T D) Bool :=
  if dims.size != 0 && widthsMatch dims.toList rows.toList
      && path.length == maxLogHeight dims.toList
      && decide (index < 2 ^ maxLogHeight dims.toList) then
    (groupDigestM dims.toList rows.toList (maxLogHeight dims.toList)).bind fun leaf =>
      (climbM dims.toList rows.toList (maxLogHeight dims.toList) index leaf path).bind
        fun digest => .pure (digest == root)
  else .pure false

/-- The check of one query of an opening at several indices: `verifyOpeningM` on
the index, the rows and the path of that query, or `false` if one is missing. -/
def verifyQueryM [DecidableEq D] (root : D) (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (paths : Array (List D)) (query : ℕ) :
    OracleComp (MerkleAnswer Msg Chal T D) Bool :=
  match indices[query]?, openedRows[query]?, paths[query]? with
  | some index, some rows, some path => verifyOpeningM root dims index rows path
  | _, _, _ => .pure false

/-- `Merkle.verifyOpenings` as an oracle computation: check that there are as
many rows and paths as indices, then check the queries in order, until one
fails. -/
def verifyOpeningsM [DecidableEq D] (root : D) (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (paths : Array (List D)) :
    OracleComp (MerkleAnswer Msg Chal T D) Bool :=
  if openedRows.size == indices.size && paths.size == indices.size then
    allM ((List.range indices.size).map (verifyQueryM root dims indices openedRows paths))
  else .pure false

/-! ## Refinement: against a function, the checks are the executable ones -/

section Run

variable (f : ∀ x : FSQuery Msg Chal (HashQuery T D), MerkleAnswer Msg Chal T D x)

namespace MerkleRO

/-- Against `f`, the query for a hash of entries gives `(hasherOf f).hashRows`. -/
theorem run_hashRowsM (xs : Array T) : (hashRowsM xs).run f = (hasherOf f).hashRows xs := rfl

/-- Against `f`, the query for a compression gives `(hasherOf f).compress`. -/
theorem run_compressM (a b : D) : (compressM a b).run f = (hasherOf f).compress a b := rfl

/-- Against `f`, `groupDigestM` computes `Merkle.groupDigest`. -/
theorem run_groupDigestM (dims : List Dimensions) (rows : List (Array T)) (h : ℕ) :
    (groupDigestM dims rows h).run f = groupDigest (hasherOf f) dims rows h := rfl

/-- Against `f`, `injectM` computes `Merkle.inject`. -/
theorem run_injectM (dims : List Dimensions) (rows : List (Array T)) (h : ℕ) (digest : D) :
    (injectM dims rows h digest).run f = inject (hasherOf f) dims rows h digest := by
  unfold injectM inject
  split
  · rw [run_bind, run_groupDigestM, run_compressM]
  · rfl

/-- Against `f`, `parentM` computes `Merkle.parent`. -/
theorem run_parentM (index : ℕ) (digest sibling : D) :
    (parentM index digest sibling).run f = parent (hasherOf f) index digest sibling := by
  unfold parentM parent
  split <;> rfl

/-- Against `f`, `climbM` computes `Merkle.climb`. -/
theorem run_climbM (dims : List Dimensions) (rows : List (Array T)) :
    ∀ (path : List D) (h index : ℕ) (digest : D),
      (climbM dims rows h index digest path).run f
        = climb (hasherOf f) dims rows h index digest path
  | [], _, _, _ => rfl
  | sibling :: path, h, index, digest => by
    rw [climbM, run_bind, run_bind, run_parentM, run_injectM, run_climbM dims rows path, climb]

/-- Against `f`, `allM` is the conjunction of the results. -/
theorem run_allM {X : Type v} {Y : X → Type w} (g : ∀ x, Y x) :
    ∀ cs : List (OracleComp Y Bool), (allM cs).run g = cs.all fun c => c.run g
  | [] => rfl
  | c :: cs => by
    rw [allM, run_bind, List.all_cons]
    cases c.run g
    · rfl
    · rw [ite_eq_left rfl, run_allM g cs, Bool.true_and]

end MerkleRO

variable [DecidableEq D]

/-- **Refinement of the check of one opening.** Against a total answer function
`f`, `verifyOpeningM` returns what the executable `Merkle.verifyOpening` returns
for the hasher `hasherOf f`. -/
theorem run_verifyOpeningM (root : D) (dims : Array Dimensions) (index : ℕ)
    (rows : Array (Array T)) (path : List D) :
    (verifyOpeningM root dims index rows path).run f
      = Merkle.verifyOpening (hasherOf f) root dims index rows path := by
  unfold verifyOpeningM
  rw [Merkle.verifyOpening]
  split
  · next hshape =>
    rw [run_bind, run_bind, run_groupDigestM, run_climbM, run_pure, hshape, Bool.true_and]
  · next hshape =>
    rw [run_pure, (Bool.not_eq_true _).mp hshape, Bool.false_and]

/-- Against `f`, the check of one query of an opening at several indices is the
executable check of that query. -/
theorem run_verifyQueryM (root : D) (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (paths : Array (List D)) (query : ℕ) :
    (verifyQueryM root dims indices openedRows paths query).run f
      = match indices[query]?, openedRows[query]?, paths[query]? with
        | some index, some rows, some path =>
          Merkle.verifyOpening (hasherOf f) root dims index rows path
        | _, _, _ => false := by
  unfold verifyQueryM
  split
  · exact run_verifyOpeningM f root dims _ _ _
  · rfl

/-- **Refinement of the check of an opening at several indices.** Against a
total answer function `f`, `verifyOpeningsM` returns what the executable
`Merkle.verifyOpenings` returns for the hasher `hasherOf f`. -/
theorem run_verifyOpeningsM (root : D) (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (paths : Array (List D)) :
    (verifyOpeningsM root dims indices openedRows paths).run f
      = Merkle.verifyOpenings (hasherOf f) root dims indices openedRows paths := by
  unfold verifyOpeningsM Merkle.verifyOpenings
  split
  · next hsize =>
    rw [run_allM, List.all_map, hsize, Bool.true_and]
    exact congrArg _ (funext (run_verifyQueryM f root dims indices openedRows paths))
  · next hsize =>
    rw [run_pure, (Bool.not_eq_true _).mp hsize, Bool.false_and]

/-- The refinement in terms of the commitment scheme the verifier is written
against: `verifyOpeningsM` returns what `verifyMultiBatch` of the Merkle scheme
over `hasherOf f` returns. -/
theorem run_verifyOpeningsM_eq_verifyMultiBatch (root : D) (dims : Array Dimensions)
    (indices : Array ℕ) (openedRows : Array (Array (Array T))) (paths : Array (List D)) :
    (verifyOpeningsM root dims indices openedRows paths).run f
      = (merkleMmcs (hasherOf f)).verifyMultiBatch root dims indices openedRows paths :=
  run_verifyOpeningsM f root dims indices openedRows paths

end Run

/-! ## Query bounds -/

namespace MerkleRO

/-- The query for a hash of entries is one query. -/
theorem queryBound_hashRowsM (xs : Array T) :
    (hashRowsM (Msg := Msg) (Chal := Chal) (D := D) xs).QueryBound 1 :=
  queryBound_query _

/-- The query for a compression is one query. -/
theorem queryBound_compressM (a b : D) :
    (compressM (Msg := Msg) (Chal := Chal) (T := T) a b).QueryBound 1 :=
  queryBound_query _

/-- An injection takes at most two queries. -/
theorem queryBound_injectM (dims : List Dimensions) (rows : List (Array T)) (h : ℕ)
    (digest : D) :
    (injectM (Msg := Msg) (Chal := Chal) dims rows h digest).QueryBound 2 := by
  unfold injectM
  split
  · exact (queryBound_hashRowsM _).bind fun group => queryBound_compressM digest group
  · trivial

/-- The compression with a sibling takes one query. -/
theorem queryBound_parentM (index : ℕ) (digest sibling : D) :
    (parentM (Msg := Msg) (Chal := Chal) (T := T) index digest sibling).QueryBound 1 := by
  unfold parentM
  split <;> exact queryBound_compressM _ _

/-- A climb takes at most three queries per level. -/
theorem queryBound_climbM (dims : List Dimensions) (rows : List (Array T)) :
    ∀ (path : List D) (h index : ℕ) (digest : D),
      (climbM (Msg := Msg) (Chal := Chal) dims rows h index digest path).QueryBound
        (3 * path.length)
  | [], _, _, _ => trivial
  | sibling :: path, h, index, digest => by
    refine QueryBound.mono ((queryBound_parentM index digest sibling).bind fun node =>
      (queryBound_injectM dims rows (h - 1) node).bind fun digest' =>
        queryBound_climbM dims rows path (h - 1) (index / 2) digest') ?_
    rw [List.length_cons]
    omega

/-- `allM` takes at most `n` queries per computation, if each takes at most `n`. -/
theorem queryBound_allM {X : Type v} {Y : X → Type w} {n : ℕ} :
    ∀ cs : List (OracleComp Y Bool), (∀ c ∈ cs, c.QueryBound n) →
      (allM cs).QueryBound (cs.length * n)
  | [], _ => trivial
  | c :: cs, h => by
    refine QueryBound.mono ((h c List.mem_cons_self).bind fun b => ?_)
      (le_of_eq (Nat.succ_mul cs.length n ▸ Nat.add_comm n (cs.length * n)))
    cases b
    · trivial
    · exact queryBound_allM cs fun c' hc' => h c' (List.mem_cons_of_mem c hc')

end MerkleRO

variable [DecidableEq D]

/-- **Query bound of the check of one opening.** The check takes at most
`3 * maxLogHeight dims + 1` queries: one for the leaf, and for each level one
compression with the sibling and at most two queries for an injection. -/
theorem queryBound_verifyOpeningM (root : D) (dims : Array Dimensions) (index : ℕ)
    (rows : Array (Array T)) (path : List D) :
    (verifyOpeningM (Msg := Msg) (Chal := Chal) root dims index rows path).QueryBound
      (3 * maxLogHeight dims.toList + 1) := by
  unfold verifyOpeningM
  split
  · next hshape =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    refine QueryBound.mono ((queryBound_hashRowsM _).bind fun leaf =>
      (queryBound_climbM dims.toList rows.toList path _ index leaf).bind (m := 0)
        fun _ => trivial) ?_
    rw [hshape.1.2]
    omega
  · trivial

/-- The check of one query of an opening at several indices takes at most
`3 * maxLogHeight dims + 1` queries. -/
theorem queryBound_verifyQueryM (root : D) (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (paths : Array (List D)) (query : ℕ) :
    (verifyQueryM (Msg := Msg) (Chal := Chal) root dims indices openedRows paths query).QueryBound
      (3 * maxLogHeight dims.toList + 1) := by
  unfold verifyQueryM
  split
  · exact queryBound_verifyOpeningM root dims _ _ _
  · trivial

/-- **Query bound of the check of an opening at several indices.** The check
takes at most `3 * maxLogHeight dims + 1` queries per index. -/
theorem queryBound_verifyOpeningsM (root : D) (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (paths : Array (List D)) :
    (verifyOpeningsM (Msg := Msg) (Chal := Chal) root dims indices openedRows paths).QueryBound
      (indices.size * (3 * maxLogHeight dims.toList + 1)) := by
  unfold verifyOpeningsM
  split
  · have h := queryBound_allM (n := 3 * maxLogHeight dims.toList + 1)
      ((List.range indices.size).map
        (verifyQueryM (Msg := Msg) (Chal := Chal) root dims indices openedRows paths))
      fun c hc => by
        obtain ⟨query, _, rfl⟩ := List.mem_map.mp hc
        exact queryBound_verifyQueryM root dims indices openedRows paths query
    rwa [List.length_map, List.length_range] at h
  · trivial

end CertiFri.Oracle
