import CertiFriProofs.Exec.Arith
import CertiFriProofs.Exec.Checks
import CertiFriProofs.Exec.Transcript
import CertiFriProofs.Theory.Compiled.Soundness

/-!
# Soundness of the executable verifier

The executable verifier `Fri.verify` (`CertiFri/Verifier.lean`) accepts only
when the model verifier of the security theory does, and so inherits its
soundness in the random-oracle model.

## Results

* `run_model_of_accepts` (refinement): if `Fri.verify`, run with the Merkle
  commitment schemes over the hash functions of an oracle `f` and with the
  idealised challenger over `f`, accepts a statement and a proof, then the
  model verifier accepts the corresponding transcript against `f`.
* `soundness`: the probability that the executable verifier accepts claims
  that fail is at most the bound of `Compiled.Params.soundness_grind`.
* `soundness_of_relDist`: the same with the folding hypothesis proved, under
  `4 * δ + (1 / 2) ^ logBlowup ≤ 1`.

## The experiment

The parameters and the shape of the claims are fixed. An adversary with access
to the oracle outputs an `Attempt`: commitments, opening points, claimed
values and a proof. Then the challenge queries of the transcript and the hash
queries of the verification are made (`experiment`; they are made by running
the model verifier). The event of the theorems is about the final log `l` of
this run: *some* total answer function `f` that agrees with `l` makes the
executable verifier accept the attempt, and the claims fail for the functions
that the hash queries of `l` commit to. So the bound covers every way of
answering the queries that were not made.

## What is assumed

* The hypotheses of `Compiled.Params.soundness_grind`: the random-oracle model
  with chained challenges, and the proximity hypotheses `CurveMCA` and
  `StepMCA`.
* `FieldModel`: the executable fields implement a field `K`, with every
  element of `K` represented. `WellFormed`: the generator of the first domain
  is a primitive root of unity of its order and the coset shift is not zero.
* The primitives of the verifier are the ideal ones: a row is hashed as the
  oracle's answer to the row of its values in `K` (`inputHasher`, `friHasher`),
  and the challenger is `freeChallenger`, whose challenges are the oracle's
  answers to everything absorbed so far. That a concrete hash function and a
  concrete challenger behave like these is not proved.
* The commitment proofs hold one Merkle path per query (`merkleMmcs`).

## What is not covered

* The Plonky3 instantiation (`CertiFriP3`): that its field arithmetic is a
  `FieldModel`, and anything about BLAKE3 or its challenger.
* An adversary that chooses the shape of the claims. The shape is fixed before
  the adversary runs, and is not absorbed into the transcript.
* Completeness: that honest proofs are accepted is tested, not proved.
-/

namespace CertiFri.Exec

open Oracle OracleComp Fri
open PcsRbr (Chal GrindChal ClaimsFail PowPasses ungrind alphaOf betasOf queriesOf)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- What an adversary outputs: a statement of the public shape, and a proof
whose commitment proofs hold one Merkle path per query. -/
structure Attempt (F EF D : Type) where
  /-- One commitment per input batch. -/
  commitments : Array D
  /-- The opening points. -/
  points : Array EF
  /-- The claimed values. -/
  values : Array EF
  /-- The opening proof. -/
  proof : FriProof F EF D (Array (List D)) (Array (List D))

/-- The raw messages of an attempt: what the verifier absorbs in each round. -/
def Attempt.messages (params : FriParams) (shape : ClaimShape) (a : Attempt F EF D) :
    ℕ → RawMsg F EF D :=
  Exec.messages params shape a.commitments a.points a.values a.proof

/-- The answer types of the oracle of the experiment: a challenge query of
round `i` is answered by `powBits params shape i` proof-of-work bits and the
challenge of the round, a hash query by a digest. -/
abbrev OracleAnswer :=
  MerkleAnswer (RawMsg F EF D)
    (GrindChal (powBits params shape)
      (Chal (modelParams m params shape wf).ldt (modelParams m params shape wf).queries)) K D

/-- **The executable verifier against an oracle.** `Fri.verify` on an attempt,
where the commitment schemes are Merkle trees over the hash functions of the
answer function `f`, and the challenger is the idealised challenger over `f`. -/
noncomputable def accepts (f : ∀ x, OracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D) :
    Bool :=
  Fri.verify (merkleMmcs (inputHasher m (hasherOf f))) (merkleMmcs (friHasher m (hasherOf f)))
    (freeChallenger (modelParams m params shape wf) (powBits params shape) f m) FreeState.init
    params shape a.commitments a.points a.values a.proof

/-! ## Refinement -/

omit [DecidableEq D] in
/-- The transcript of an attempt along the Fiat–Shamir chain of `f` holds the
raw messages of the attempt. -/
theorem msgAt_fsTranscript (f : ∀ x, OracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    {j : ℕ} (hj : j ≤ numRounds params shape + 1) :
    Compiled.msgAt (ungrind (fsTranscript f (a.messages params shape)
      ((modelParams m params shape wf).rounds + 2))) j = a.messages params shape j := by
  refine Compiled.msgAt_eq_of_getElem? ?_
  rw [Compiled.msgs_ungrind, fsTranscript_msgs, List.getElem?_map,
    List.getElem?_range (show j < (modelParams m params shape wf).rounds + 2 from
      Nat.lt_succ_of_le hj)]
  rfl

/-- **Refinement.** If the executable verifier accepts an attempt against the
oracle `f`, the model verifier accepts, against `f`, the transcript of the
attempt along the Fiat–Shamir chain of `f`. -/
theorem run_model_of_accepts (f : ∀ x, OracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (h : accepts m params shape wf f a = true) :
    ((modelParams m params shape wf).verifyGrindView (powBits params shape)
      (view m params shape) (modelProof m params shape a.proof)
      (fsTranscript f (a.messages params shape)
        ((modelParams m params shape wf).rounds + 2))).run f = true := by
  unfold accepts Fri.verify at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hshape, hwith⟩ := h
  obtain ⟨hα, hβ, hpow, -, hidx⟩ :=
    transcript_free m params shape wf f a.commitments a.points a.values a.proof hshape
  have hag : Agrees m params shape a.commitments a.points a.values a.proof
      (transcript (freeChallenger (modelParams m params shape wf) (powBits params shape) f m)
        FreeState.init params shape a.commitments a.points a.values a.proof)
      (fun j => view m params shape (Compiled.msgAt (ungrind (fsTranscript f
        (a.messages params shape) ((modelParams m params shape wf).rounds + 2))) j))
      (alphaOf (ungrind (fsTranscript f (a.messages params shape)
        ((modelParams m params shape wf).rounds + 2))))
      (betasOf (ungrind (fsTranscript f (a.messages params shape)
        ((modelParams m params shape wf).rounds + 2))))
      (fun k => (modelParams m params shape wf).indexOf
        (queriesOf (ungrind (fsTranscript f (a.messages params shape)
          ((modelParams m params shape wf).rounds + 2))) k)) :=
    { msg := fun j hj => by rw [msgAt_fsTranscript m params shape wf f a hj]; rfl
      alpha := hα.symm
      beta := fun i _ => (hβ i).symm
      index := fun k => (hidx k).symm }
  obtain ⟨hpowOk, hchecks⟩ := modelChecks_of_verifyWith_aux m params shape wf (hasherOf f) hshape
    hag (fun t hok => finalCheck_of_queryResult m params shape wf hshape hag t hok)
    (fun t i hi => rows_queryResult m params shape wf hshape hag t hi) hwith
  refine ((modelParams m params shape wf).run_verifyGrindView _ _ f _ _).mpr ⟨hpow hpowOk, ?_⟩
  exact ((modelParams m params shape wf).run_verifyWith f _ _ _ _ _).trans hchecks

/-! ## Soundness -/

section Soundness

variable [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- **The soundness experiment.** The adversary runs and returns `a`, of which
`attempt a` is its statement and proof. Then the challenge of every round of
the transcript is queried, and the hash queries of the verification are made,
by running the model verifier. The result is `a` and the model verifier's
verdict. -/
noncomputable def experiment {A : Type*}
    (adv : OracleComp (OracleAnswer (D := D) m params shape wf) A) (attempt : A → Attempt F EF D) :
    OracleComp (OracleAnswer (D := D) m params shape wf) (A × Bool) :=
  (modelParams m params shape wf).experimentGrindView (powBits params shape)
    (view m params shape) adv (fun a => (attempt a).messages params shape)
    (fun a => modelProof m params shape (attempt a).proof)


/-- A function that agrees with a log is its own completion of the log. -/
theorem toFun_eq_self {X : Type} {Y : X → Type} [DecidableEq X] {l : Log Y} {f : ∀ x, Y x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y) : l.toFun f = f := by
  funext x
  cases hx : l.dlookup x with
  | none => rw [Log.toFun, hx, Option.getD_none]
  | some y => rw [Log.toFun_of_dlookup f hx, hf x y hx]

omit [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] [Fintype K]
  [Fintype D] [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] in
/-- There is no proof of work before the batching challenge. -/
theorem powBits_zero : powBits params shape 0 = 0 := by
  simp [powBits]

omit [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] [Fintype K]
  [Fintype D] [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] in
/-- Each folding challenge comes after `commitPowBits` bits of proof of work. -/
theorem powBits_succ_of_lt {i : ℕ} (hi : i < numRounds params shape) :
    powBits params shape (i + 1) = params.commitPowBits := by
  simp only [powBits, Nat.succ_ne_zero, ↓reduceIte]
  rw [ite_eq_left (Nat.succ_le_of_lt hi)]

omit [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] [Fintype K]
  [Fintype D] [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] in
/-- The query indices come after `queryPowBits` bits of proof of work. -/
theorem powBits_last :
    powBits params shape (numRounds params shape + 1) = params.queryPowBits := by
  simp only [powBits, Nat.succ_ne_zero, ↓reduceIte]
  rw [ite_eq_right (Nat.not_succ_le_self _)]

/-- **Soundness of the executable verifier in the random-oracle model.**

*Statement.* Fix the parameters and the shape of the claims. Whatever the
adversary, as long as it makes at most `Q` oracle queries: the probability that
the executable verifier accepts its attempt while the claims of the attempt
fail is at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

where `N = Q + (rounds + 2) + P.verifierQueries` counts the oracle queries of
the experiment, `batches = shape.length`, `rounds = numRounds params shape`,
and `P.verifierQueries = (batches + rounds) * (numQueries * (3 * n + 1))` with
`n = logMaxHeight params.logBlowup shape`.

*"The executable verifier accepts".* Some total answer function `f` that agrees
with the final log `l` of the experiment makes `Fri.verify` return `true` on
the attempt, when its commitment schemes are Merkle trees over the hash
functions of `f` and its challenger is the idealised challenger over `f`
(`accepts`). The log holds the answers to the adversary's queries, to the
challenge queries of the attempt's transcript and to the hash queries of its
verification.

*"The claims fail".* As in `Compiled.Params.soundness`, for the model
parameters `P = modelParams m params shape wf`. Level `j` holds the claims
`levelClaims … j` of the shape, in order. The claim of a `ClaimRef` `c` is about
the function on the coset of its level whose value at the point of index `i` is
the entry `c.col` of row `i` of matrix `c.matrix` that the hash queries of `l`
open under commitment `c.batch`; its opening point is `points[c.pointIdx]` and
its claimed value `values[c.valueIdx]`, as elements of `K`
(`point_msg_zero`, `value_msg_zero`). `ClaimsFail` says that at some level there
is no set of at least `θ` of the coset on which every claimed function of the
level agrees, except possibly at its opening point, with a polynomial of degree
at most `2 ^ (rounds - j) * finalPolyLen` that takes the claimed value at the
opening point.

*Assumptions.* `0 ≤ θ`; the batching hypothesis `hmca` and the folding
hypothesis `hstep` for the model parameters; `εmax` bounds the error of every
round: `∑ j ≤ rounds, εα j` for the batching round, `εβ i / 2 ^ commitPowBits`
for folding round `i`, and `θ ^ numQueries / 2 ^ queryPowBits` for the query
round. The module documentation lists what is assumed of the fields and of the
primitives. -/
theorem soundness {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ (modelParams m params shape wf).rounds, CurveMCA ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n j).image ((modelParams m params shape wf).shift * ·))
      (2 ^ ((modelParams m params shape wf).rounds - j) * (modelParams m params shape wf).finalDegree) ((modelParams m params shape wf).numClaims j) θ (εα j))
    (hstep : ∀ i < (modelParams m params shape wf).rounds, StepMCA (twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n i) (twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n (i + 1))
      (2 ^ ((modelParams m params shape wf).rounds - (i + 1)) * (modelParams m params shape wf).finalDegree) θ (εβ i))
    (hα : ∑ j ∈ Finset.range ((modelParams m params shape wf).rounds + 1), εα j ≤ εmax)
    (hβ : ∀ i < (modelParams m params shape wf).rounds, εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims (view m params shape (firstMessage (attempt res.1).commitments
            (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) * εmax +
        (((modelParams m params shape wf).batches + 1) * ((modelParams m params shape wf).rounds + 2) + 3) * (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) *
          (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries - 1) / (2 * Fintype.card D) :=
  (modelParams m params shape wf).soundness_grind_view_of_imp (powBits params shape)
    (view m params shape) hθ hmca hstep
    (by rw [powBits_zero, pow_zero, div_one]; exact hα)
    (fun i hi => by rw [powBits_succ_of_lt params shape hi]; exact hβ i hi)
    (by rw [show (modelParams m params shape wf).rounds = numRounds params shape from rfl,
      powBits_last]; exact hq)
    hadv (fun a => (attempt a).messages params shape)
    (fun a => modelProof m params shape (attempt a).proof)
    (fun a l => ∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
      (∀ x y, l.dlookup x = some y → f x = y) ∧ accepts m params shape wf f (attempt a) = true)
    (fun out l b l' hexp hver hE => by
      obtain ⟨f, hf, hacc⟩ := hE
      have hrun := (modelParams m params shape wf).run_verifyGrindView_of_outcome hexp hver f
      rw [toFun_eq_self hf] at hrun
      exact hrun.symm.trans (run_model_of_accepts m params shape wf f _ hacc))

/-- **Soundness of the executable verifier, with the folding hypothesis
proved.** Let no committed column be shorter than the final height, and let
`δ ≥ 0` with `4 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then `soundness` holds at
agreement `θ = 1 - δ` with no hypothesis on the folding rounds: the error of a
folding round is at most `2 * (δ * 2 ^ (n - 1) + 1) / |K|`, divided by
`2 ^ commitPowBits`. The batching hypothesis `hmca` remains. -/
theorem soundness_of_relDist
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 4 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εα : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ (modelParams m params shape wf).rounds, CurveMCA ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n j).image ((modelParams m params shape wf).shift * ·))
      (2 ^ ((modelParams m params shape wf).rounds - j) * (modelParams m params shape wf).finalDegree) ((modelParams m params shape wf).numClaims j) (1 - δ) (εα j))
    (hα : ∑ j ∈ Finset.range ((modelParams m params shape wf).rounds + 1), εα j ≤ εmax)
    (hβ : 2 * (δ * 2 ^ ((modelParams m params shape wf).n - 1) + 1) / Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift (1 - δ)
          ((modelParams m params shape wf).claims (view m params shape (firstMessage (attempt res.1).commitments
            (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) * εmax +
        (((modelParams m params shape wf).batches + 1) * ((modelParams m params shape wf).rounds + 2) + 3) * (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) *
          (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries - 1) / (2 * Fintype.card D) :=
  (modelParams m params shape wf).soundness_grind_view_of_imp_of_relDist (powBits params shape)
    (view m params shape) (logBlowup := params.logBlowup) (logFinalPolyLen := params.logFinalPolyLen)
    (by
      show logMaxHeight params.logBlowup shape =
        numRounds params shape + params.logBlowup + params.logFinalPolyLen
      unfold numRounds FriParams.logFinalHeight at *
      omega)
    rfl hδ hrate hmca
    (by rw [powBits_zero, pow_zero, div_one]; exact hα)
    (fun i hi => by rw [powBits_succ_of_lt params shape hi]; exact hβ)
    (by rw [show (modelParams m params shape wf).rounds = numRounds params shape from rfl,
      powBits_last]; exact hq)
    hadv (fun a => (attempt a).messages params shape)
    (fun a => modelProof m params shape (attempt a).proof)
    (fun a l => ∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
      (∀ x y, l.dlookup x = some y → f x = y) ∧ accepts m params shape wf f (attempt a) = true)
    (fun out l b l' hexp hver hE => by
      obtain ⟨f, hf, hacc⟩ := hE
      have hrun := (modelParams m params shape wf).run_verifyGrindView_of_outcome hexp hver f
      rw [toFun_eq_self hf] at hrun
      exact hrun.symm.trans (run_model_of_accepts m params shape wf f _ hacc))

end Soundness

end CertiFri.Exec
