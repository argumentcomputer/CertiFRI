import CertiFriProofs.Theory.Oracle.MerkleOpens

/-!
# Binding of a Merkle commitment, located in the log

`Merkle.verifyOpening_binding` says that two accepted openings that disagree on
a row give a collision of the hasher. For a random oracle that is not enough:
the bound on collisions is about the queries that were made. This file proves
binding for the openings a log holds (`Opens`), with the collision among the
entries of that log.

## Results

* `Opens.row_eq_or_logCollision`: two openings in a log `l` under one root that
  address the same row of matrix `m` show the same row of it, or `l` has a
  collision: two hash entries with different queries and the same answer
  (`LogCollision hashObs l`). `logCollision_of_opens_of_ne` and `Opens.row_eq`
  are the two ways to read it.
* `Opens.rows_eq_or_logCollision`: two openings at the same index show the same
  rows of every matrix, or the log has a collision.
* `prob_logCollision_hashObs_le`: a computation that makes at most `Q` queries
  from the empty log leaves a log with a collision with probability at most
  `1 / card D * Q * (Q - 1) / 2`, which is `Q * (Q - 1) / (2 * card D)`
  (`prob_logCollision_hashObs_le'`).

The proof applies the executable theorem to the hasher of the log
(`MerkleRO.logHasher`), which is injective except on two logged queries with
the same answer.

A collision here is between any two hash entries, also between a `rows` and a
`node` entry.

There are no assumptions on the log. The probability bound is for a run from
the empty log against a uniformly random oracle with digests in a finite,
nonempty `D`.

Not covered: the bound from a log that is not empty (`prob_logCollision_le_sum`
gives it for a log without a collision).
-/

namespace CertiFri.Oracle

universe u w

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

open OracleComp Merkle MerkleRO

section Binding

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))]
  {l : Log (MerkleAnswer Msg Chal T D)} {root : D} {dims : Array Dimensions}
  {index index' : ℕ} {rows rows' : Array (Array T)}

/-- **Binding, located in the log.** Two openings in the log `l` under one root
that address the same row of matrix `m` show the same row of it, or `l` has two
hash entries with different queries and the same answer. -/
theorem Opens.row_eq_or_logCollision (h : Opens l root dims index rows)
    (h' : Opens l root dims index' rows') {m : ℕ} {d : Dimensions} (hd : dims[m]? = some d)
    (hindex : index >>> (maxLogHeight dims.toList - d.logHeight)
      = index' >>> (maxLogHeight dims.toList - d.logHeight)) :
    rows[m]? = rows'[m]? ∨ LogCollision hashObs l := by
  classical
  obtain ⟨path, hpath⟩ := h
  obtain ⟨path', hpath'⟩ := h'
  exact (Merkle.verifyOpening_binding hpath hpath' hd hindex).imp id logCollision_of_collides

/-- Two openings in a log under one root that address the same row of matrix
`m` and show different rows of it give a collision of the log. -/
theorem logCollision_of_opens_of_ne (h : Opens l root dims index rows)
    (h' : Opens l root dims index' rows') {m : ℕ} {d : Dimensions} (hd : dims[m]? = some d)
    (hindex : index >>> (maxLogHeight dims.toList - d.logHeight)
      = index' >>> (maxLogHeight dims.toList - d.logHeight))
    (hne : rows[m]? ≠ rows'[m]?) : LogCollision hashObs l :=
  (h.row_eq_or_logCollision h' hd hindex).resolve_left hne

/-- In a log without a collision, two openings under one root that address the
same row of matrix `m` show the same row of it. -/
theorem Opens.row_eq (hl : ¬ LogCollision hashObs l) (h : Opens l root dims index rows)
    (h' : Opens l root dims index' rows') {m : ℕ} {d : Dimensions} (hd : dims[m]? = some d)
    (hindex : index >>> (maxLogHeight dims.toList - d.logHeight)
      = index' >>> (maxLogHeight dims.toList - d.logHeight)) :
    rows[m]? = rows'[m]? :=
  (h.row_eq_or_logCollision h' hd hindex).resolve_right hl

/-- Two openings in a log under one root at the same index show the same rows of
every matrix, or the log has a collision. -/
theorem Opens.rows_eq_or_logCollision (h : Opens l root dims index rows)
    (h' : Opens l root dims index rows') : rows = rows' ∨ LogCollision hashObs l := by
  classical
  obtain ⟨path, hpath⟩ := h
  obtain ⟨path', hpath'⟩ := h'
  exact (Merkle.verifyOpening_binding_index hpath hpath').imp id logCollision_of_collides

end Binding

/-! ## The probability of a collision -/

section Bound

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))] [∀ i, Fintype (Chal i)]
  [∀ i, Nonempty (Chal i)] [Fintype D] [Nonempty D] {α : Type w}

omit [DecidableEq (FSQuery Msg Chal (HashQuery T D))] [∀ i, Nonempty (Chal i)] [Nonempty D] in
/-- The answer to a query is observed as a given digest for at most one answer
in `card D`. -/
theorem fractionLE_hashObs (x : FSQuery Msg Chal (HashQuery T D)) (z : D) :
    FractionLE (fun y : MerkleAnswer Msg Chal T D x => hashObs x y = some z)
      (1 / Fintype.card D) :=
  FSQuery.fractionLE_liftObs (by positivity)
    (fun _ z => (FractionLE.eq z).mono_left fun _ hy => Option.some.inj hy) x z

/-- **Collisions of the hash oracle.** A computation that makes at most `Q`
queries from the empty log leaves a log with two hash entries with different
queries and the same answer with probability at most
`1 / card D * Q * (Q - 1) / 2`. -/
theorem prob_logCollision_hashObs_le {c : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ}
    (hc : c.QueryBound Q) :
    prob (fun _ l => LogCollision hashObs l) c [] ≤ 1 / Fintype.card D * Q * (Q - 1) / 2 :=
  prob_logCollision_le (by positivity) fractionLE_hashObs hc

/-- The collision bound in the form `Q * (Q - 1) / (2 * card D)`. -/
theorem prob_logCollision_hashObs_le' {c : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ}
    (hc : c.QueryBound Q) :
    prob (fun _ l => LogCollision hashObs l) c [] ≤ Q * (Q - 1) / (2 * Fintype.card D) :=
  (prob_logCollision_hashObs_le hc).trans (le_of_eq (by ring))

end Bound

end CertiFri.Oracle
