import CertiFriProofs.Theory.Fold

/-!
# Completeness of the query check

The honest prover, as polynomials. Given the input polynomial `P i` of each
level (zero when no input has that height) and the challenges `β`, the
codeword the honest prover commits to at level `i + 1` is the fold of the one
at level `i` plus `β i ^ 2` times the input of level `i + 1`.

The file proves that these polynomials respect the degree bound of every
level, that the final one is a codeword on the last domain, and that the
verifier's query check accepts their evaluations at every point of the first
domain, for every choice of challenges. The query check reads the functions
only on the domains, so it also accepts any functions that agree with the
honest polynomials there (`queryAccepts_of_eq_honestPoly`).

It assumes nothing beyond the `LdtInstance` itself. It does not cover the
Merkle openings or the Fiat–Shamir transcript: the committed codewords are
functions, as everywhere in the oracle model.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-- A point of the first domain, squared `i` times, lies in the domain of
level `i`. -/
theorem LdtInstance.pow_mem (S : LdtInstance F) {x : F} (hx : x ∈ S.domain 0) {i : ℕ}
    (hi : i ≤ S.rounds) : x ^ 2 ^ i ∈ S.domain i := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ, pow_mul]
    exact (S.step i hi).sq_mem _ (ih (Nat.le_of_succ_le hi))

/-- The polynomial the honest prover commits to at each level. -/
noncomputable def honestPoly (P : ℕ → F[X]) (β : ℕ → F) : ℕ → F[X]
  | 0 => P 0
  | i + 1 => foldPoly (β i) (honestPoly P β i) + C (β i ^ 2) * P (i + 1)

/-- If every input polynomial respects the degree bound of its level, so does
every polynomial of the honest prover. -/
theorem degree_honestPoly_lt (S : LdtInstance F) {P : ℕ → F[X]} (β : ℕ → F)
    (hP : ∀ i ≤ S.rounds, (P i).degree < S.degree i) :
    ∀ i ≤ S.rounds, (honestPoly P β i).degree < S.degree i := by
  intro i
  induction i with
  | zero => exact hP 0
  | succ i ih =>
    intro hi
    have h := ih (Nat.le_of_succ_le hi)
    rw [S.degree_step i hi] at h
    exact (degree_add_le _ _).trans_lt
      (max_lt (degree_foldPoly_lt _ h) (Fold.degree_C_mul_lt _ (hP _ hi)))

/-- At every level, the evaluation of the honest prover's polynomial is a
codeword. -/
theorem isCodeword_honestPoly (S : LdtInstance F) {P : ℕ → F[X]} (β : ℕ → F)
    (hP : ∀ i ≤ S.rounds, (P i).degree < S.degree i) {i : ℕ} (hi : i ≤ S.rounds) :
    IsCodeword (S.domain i) (S.degree i) (fun y => (honestPoly P β i).eval y) :=
  ⟨honestPoly P β i, degree_honestPoly_lt S β hP i hi, fun _ _ => rfl⟩

/-- The final message of the honest prover is a codeword on the last domain. -/
theorem isCodeword_honestPoly_rounds (S : LdtInstance F) {P : ℕ → F[X]} (β : ℕ → F)
    (hP : ∀ i ≤ S.rounds, (P i).degree < S.degree i) :
    IsCodeword (S.domain S.rounds) (S.degree S.rounds)
      (fun y => (honestPoly P β S.rounds).eval y) :=
  isCodeword_honestPoly S β hP le_rfl

/-- Every query accepts inputs and committed functions that agree, on the domain
of each level, with the input polynomials and with the honest prover's
polynomials. Their values off the domains do not matter. -/
theorem queryAccepts_of_eq_honestPoly (S : LdtInstance F) (P : ℕ → F[X]) (β : ℕ → F)
    {ro c : ℕ → F → F} (hro : ∀ i ≤ S.rounds, ∀ y ∈ S.domain i, ro i y = (P i).eval y)
    (hc : ∀ i ≤ S.rounds, ∀ y ∈ S.domain i, c i y = (honestPoly P β i).eval y) {x : F}
    (hx : x ∈ S.domain 0) : QueryAccepts S.rounds ro c β x := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hc 0 (Nat.zero_le _) x hx, hro 0 (Nat.zero_le _) x hx, honestPoly]
  · have hstep := S.step i hi
    have hxi := S.pow_mem hx hi.le
    have hxi' := S.pow_mem hx (Nat.succ_le_of_lt hi)
    rw [hc (i + 1) hi _ hxi', hro (i + 1) hi _ hxi',
      foldAt_eq_eval_foldPoly hstep.two_ne_zero (β i) (hstep.ne_zero _ hxi) (hc i hi.le _ hxi)
        (hc i hi.le _ (hstep.neg_mem _ hxi)), pow_succ, pow_mul]
    simp only [honestPoly, eval_add, eval_mul, eval_C]

/-- Every query accepts the honest codewords. -/
theorem queryAccepts_honest (S : LdtInstance F) (P : ℕ → F[X]) (β : ℕ → F) {x : F}
    (hx : x ∈ S.domain 0) :
    QueryAccepts S.rounds (fun i => (P i).eval) (fun i => (honestPoly P β i).eval) β x :=
  queryAccepts_of_eq_honestPoly S P β (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hx

end CertiFri
