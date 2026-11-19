import CertiFriProofs.Theory.Compiled.SoundnessView
import CertiFriProofs.Theory.Oracle.Replay

/-!
# Soundness of the compiled protocol for two attempts

The soundness theorems of `Compiled/SoundnessView.lean` are about an adversary
that outputs one transcript, and their event is about the log right after the
verification of that transcript. Here the adversary outputs two transcripts,
both are verified, one after the other, against the same oracle, and the event
is about the final log, after both verifications. This is the form a statement
about two openings of one commitment needs.

## The experiment

`Params.experimentGrindView₂ bits view adv msgs₁ msgs₂ proofOf₁ proofOf₂`:

1. The adversary `adv` runs with access to the oracle and returns `a`. Its
   first attempt has the raw messages `msgs₁ a` and the proof data `proofOf₁ a`,
   its second attempt `msgs₂ a` and `proofOf₂ a`.
2. The challenges of the first attempt are derived along the Fiat–Shamir chain
   and the model verifier `Params.verifyGrindView` runs on it
   (`Params.experimentGrindView`).
3. The same for the second attempt.

## Results

With `N` the number of oracle queries of the whole experiment and

    bound N = N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|):

* `Params.AcceptsLog`: the acceptance event for a log. Some total answer
  function that agrees with the log makes the model verifier accept the proof
  data on the transcript that function gives along the Fiat–Shamir chain.
* `Params.accepts_of_acceptsLog`: after the derivation of the challenges of a
  transcript and its verification, let a later log without a hit satisfy
  `AcceptsLog`. Then the verdict was `true`, the proof-of-work checks pass, and
  the transcript read from the committed rows of the later log is accepted in
  the oracle model.
* `Params.soundness_grind_view_bind`: soundness for one attempt when any
  computation `rest`, with at most `R` queries, runs after the verification.
  An event of the final log that implies `AcceptsLog` and that the claims fail
  has probability at most `bound (Q + (rounds + 2) + verifierQueries + R)`.
* `Params.soundness_grind_view₂_first`, `Params.soundness_grind_view₂_second`:
  in the experiment for two attempts, the probability that one given attempt is
  accepted on the final log while its claims, read from the final log, fail is
  at most `bound N` with `N = Q + 2 * ((rounds + 2) + verifierQueries)`.
* `Params.soundness_grind_view₂`: the probability that this happens for one of
  the two attempts is at most `2 * bound N`.

## Assumptions

Those of `Params.soundness_grind_view_of_accepts`
(`Compiled/SoundnessView.lean`): the random-oracle model with chained
challenges, the proximity hypotheses `CurveMCA` (batching) and `StepMCA`
(folding), and the modelling choices of `Compiled/Read.lean` and
`Compiled/Verifier.lean`.

## Not covered

* More than two attempts. `Params.soundness_grind_view_bind` is the statement
  to iterate.
* Any relation between the two attempts: that they share commitments is a
  matter for the statement that uses this one.
* A verifier other than the model verifier: its acceptance has to imply
  `AcceptsLog`.
-/

namespace CertiFri.Compiled

open Oracle OracleComp
open PcsRbr (Chal ClaimsFail Accepts GrindChal PowPasses ungrind)

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

namespace Params

variable (P : Params F)

/-! ## Acceptance on a log -/

/-- **The model verifier accepts on the log `l`.** Some total answer function
`f` that agrees with `l` makes the model verifier `verifyGrindView` accept the
proof data `pf` on the transcript with the raw messages `ms` and the challenges
that `f` gives along the Fiat–Shamir chain. A log that extends `l` allows fewer
such functions, so the property passes from a log to its prefixes. -/
def AcceptsLog {M : Type} [DecidableEq M] (bits : ℕ → ℕ) (view : M → Msg F D P.batches)
    (pf : Proof F D P.batches P.queries) (ms : ℕ → M)
    (l : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)) : Prop :=
  ∃ f : ∀ x, MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D x,
    (∀ x y, l.dlookup x = some y → f x = y) ∧
      (P.verifyGrindView bits view pf (fsTranscript f ms (P.rounds + 2))).run f = true

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- Acceptance on a log implies acceptance on every prefix of it. -/
theorem AcceptsLog.of_prefix {M : Type} [DecidableEq M] {bits : ℕ → ℕ}
    {view : M → Msg F D P.batches} {pf : Proof F D P.batches P.queries} {ms : ℕ → M}
    {l l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)}
    (h : P.AcceptsLog bits view pf ms l') (hl : l <+: l') : P.AcceptsLog bits view pf ms l := by
  obtain ⟨f, hf, hrun⟩ := h
  exact ⟨f, fun x y hxy => hf x y (dlookup_of_prefix hxy hl), hrun⟩

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- **The verdict of the model verifier, from acceptance on a later log.** After
the adversary and the derivation of the challenges, let the model verifier
return `b` and leave the log `l₁`. If the model verifier accepts on a log that
extends `l₁`, for the adversary's messages, then `b = true`. -/
theorem verdict_of_acceptsLog {M : Type} [DecidableEq M] {bits : ℕ → ℕ}
    {view : M → Msg F D P.batches} {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A}
    {msgs : A → ℕ → M} {pf : Proof F D P.batches P.queries}
    {out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)}
    {l₀ l l₁ l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)} {b : Bool}
    (hexp : Outcome (fsExperiment (P.rounds + 2) adv msgs) l₀ out l)
    (hver : Outcome (P.verifyGrindView bits view pf out.2) l b l₁) (hl : l₁ <+: l')
    (hacc : P.AcceptsLog bits view pf (msgs out.1) l') : b = true := by
  obtain ⟨f, hf, hrun⟩ := hacc
  obtain ⟨la, -, hd⟩ := outcome_fsExperiment.mp hexp
  have ht : out.2 = fsTranscript f (msgs out.1) (P.rounds + 2) :=
    hd.eq_fsTranscript fun x y hxy => hf x y (dlookup_of_prefix hxy (hver.prefix.trans hl))
  rw [← ht] at hrun
  exact (hver.run_eq fun x y hxy => hf x y (dlookup_of_prefix hxy hl)).symm.trans hrun

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- **Acceptance on a later log without a hit is acceptance in the oracle
model.** After the adversary and the derivation of the challenges, let the
model verifier run and leave the log `l₁`, and let `l'` be a log that extends
`l₁` and has no hit, for any choice `digests` of the digests of a raw message.
If the model verifier accepts on `l'`, then every proof-of-work sample of the
transcript is zero, and the transcript without the samples, with every message
read through `view` and from the rows that `l'` commits to, is accepted by the
oracle-model protocol. -/
theorem accepts_of_acceptsLog {M : Type} [DecidableEq M] {bits : ℕ → ℕ}
    {view : M → Msg F D P.batches} {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A}
    {msgs : A → ℕ → M} {pf : Proof F D P.batches P.queries}
    {out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)}
    {l₀ l l₁ l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)} {b : Bool}
    (hexp : Outcome (fsExperiment (P.rounds + 2) adv msgs) l₀ out l)
    (hver : Outcome (P.verifyGrindView bits view pf out.2) l b l₁) (hl : l₁ <+: l')
    (hacc : P.AcceptsLog bits view pf (msgs out.1) l') {digests : M → List D} {r : ℕ}
    (hno : ¬ HasBad (Hit digests r) l') :
    PowPasses out.2 ∧
      Accepts P.ldt P.shift
        ((ungrind out.2).mapIdx fun j m => P.read j (view m) (committedRow l')) := by
  obtain rfl := P.verdict_of_acceptsLog hexp hver hl hacc
  exact P.accepts_of_outcome_verifyGrindView (hver.replay hl) hno

/-! ## One attempt, followed by any computation -/

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- The experiment for one attempt makes the adversary's queries, one query per
round, and the queries of the model verifier. -/
theorem queryBound_experimentGrindView {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries) :
    (P.experimentGrindView bits view adv msgs proofOf).QueryBound
      (Q + (P.rounds + 2) + P.verifierQueries) :=
  (queryBound_fsExperiment hadv msgs).bind fun _ =>
    (P.queryBound_verifyGrindView bits view _ _).bind (m := 0) fun _ => queryBound_pure _ _

/-- **Soundness with proof of work when a computation follows the
verification.** The experiment `experimentGrindView` runs for an adversary with
at most `Q` oracle queries, and then any computation `rest` runs on its result,
with at most `R` oracle queries. Let `E` be an event of the result of `rest`
and the final log such that, on every outcome, `E` implies that the model
verifier accepts on the final log (`AcceptsLog`) and that the claims of the
adversary's first message, read through `view` and from the final log, fail.
Then `E` has probability at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

with `N = Q + (rounds + 2) + verifierQueries + R`.

The other hypotheses are those of `soundness_grind_view_of_accepts`. -/
theorem soundness_grind_view_bind {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*} {B : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries)
    {rest : A × Bool → OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) B}
    {R : ℕ} (hrest : ∀ res, (rest res).QueryBound R)
    {E : B → Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) → Prop}
    (hE : ∀ (res : A × Bool)
      (l : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)) (b : B)
      (l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)),
      Outcome (P.experimentGrindView bits view adv msgs proofOf) [] res l →
      Outcome (rest res) l b l' → E b l' →
      P.AcceptsLog bits view (proofOf res.1) (msgs res.1) l' ∧
        ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l'))) :
    prob E ((P.experimentGrindView bits view adv msgs proofOf).bind rest) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries + R) * εmax +
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + (P.rounds + 2) + P.verifierQueries + R) *
          (Q + (P.rounds + 2) + P.verifierQueries + R - 1) / (2 * Fintype.card D) := by
  have hassoc : (P.experimentGrindView bits view adv msgs proofOf).bind rest =
      (fsExperiment (P.rounds + 2) adv msgs).bind fun out =>
        ((P.verifyGrindView bits view (proofOf out.1) out.2).bind fun b =>
          .pure (out.1, b)).bind rest :=
    OracleComp.bind_assoc _ _ _
  have h := P.soundness_grind_view_of_accepts bits view hθ hmca hstep hα hβ hq hadv msgs
    (rest := fun out =>
      ((P.verifyGrindView bits view (proofOf out.1) out.2).bind fun b =>
        .pure (out.1, b)).bind rest)
    (R := P.verifierQueries + R)
    (fun out => ((P.queryBound_verifyGrindView bits view _ _).bind (m := 0) fun _ =>
      queryBound_pure _ _).bind hrest)
    (E := E) fun out l b l' hexp hrun hb hno => by
      obtain ⟨res, l₁, hres, hrest'⟩ := outcome_bind.mp hrun
      obtain ⟨b₁, l₂, hver, hpure⟩ := outcome_bind.mp hres
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      obtain ⟨hacc, hfail⟩ := hE (out.1, b₁) l₁ b l'
        (outcome_bind.mpr ⟨out, l, hexp, outcome_bind.mpr ⟨b₁, l₁, hver, rfl, rfl⟩⟩) hrest' hb
      exact ⟨hfail, P.accepts_of_acceptsLog hexp hver hrest'.prefix hacc hno⟩
  rw [hassoc]
  have hN : (Q + (P.rounds + 2) + ((P.verifierQueries + R : ℕ) : ℝ) : ℝ) =
      Q + (P.rounds + 2) + P.verifierQueries + R := by
    push_cast
    ring
  rwa [hN] at h

/-! ## Two attempts -/

/-- **The soundness experiment for two attempts.** The adversary runs and
returns `a`. Its first attempt has the raw messages `msgs₁ a` and the proof
data `proofOf₁ a`, its second attempt `msgs₂ a` and `proofOf₂ a`. First the
challenges of the first attempt are derived along the Fiat–Shamir chain and the
model verifier `verifyGrindView` checks its proof data against the transcript
(`experimentGrindView`). Then the challenges of the second attempt are derived
and the model verifier checks its proof data. Both run against the same oracle.
The result is `a` and the two verdicts. -/
def experimentGrindView₂ {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {A : Type*}
    (adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A)
    (msgs₁ msgs₂ : A → ℕ → M) (proofOf₁ proofOf₂ : A → Proof F D P.batches P.queries) :
    OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) (A × Bool × Bool) :=
  (P.experimentGrindView bits view adv msgs₁ proofOf₁).bind fun res =>
    (derive _ (msgs₂ res.1) (P.rounds + 2)).bind fun t =>
      (P.verifyGrindView bits view (proofOf₂ res.1) t).bind fun b => .pure (res.1, res.2, b)

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- The experiment for two attempts is the experiment for the second attempt
alone, for the adversary that consists of the given adversary and the
processing of the first attempt. -/
theorem experimentGrindView₂_eq_bind {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {A : Type*}
    (adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A)
    (msgs₁ msgs₂ : A → ℕ → M) (proofOf₁ proofOf₂ : A → Proof F D P.batches P.queries) :
    P.experimentGrindView₂ bits view adv msgs₁ msgs₂ proofOf₁ proofOf₂ =
      (P.experimentGrindView bits view (P.experimentGrindView bits view adv msgs₁ proofOf₁)
        (fun res => msgs₂ res.1) (fun res => proofOf₂ res.1)).bind fun res =>
          .pure (res.1.1, res.1.2, res.2) := by
  simp only [experimentGrindView₂, experimentGrindView, fsExperiment, OracleComp.bind_assoc,
    OracleComp.pure_bind]

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- The experiment for two attempts makes the adversary's queries and, for each
attempt, one query per round and the queries of the model verifier. -/
theorem queryBound_experimentGrindView₂ {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs₁ msgs₂ : A → ℕ → M)
    (proofOf₁ proofOf₂ : A → Proof F D P.batches P.queries) :
    (P.experimentGrindView₂ bits view adv msgs₁ msgs₂ proofOf₁ proofOf₂).QueryBound
      (Q + 2 * ((P.rounds + 2) + P.verifierQueries)) :=
  ((P.queryBound_experimentGrindView bits view hadv msgs₁ proofOf₁).bind fun res =>
    (queryBound_derive (msgs₂ res.1) (P.rounds + 2)).bind fun _ =>
      (P.queryBound_verifyGrindView bits view _ _).bind (m := 0) fun _ =>
        queryBound_pure _ _).mono (by omega)

/-- **Soundness for the first of two attempts, at the final log.** In the
experiment `experimentGrindView₂`, with an adversary that makes at most `Q`
oracle queries: the probability that the model verifier accepts the first
attempt on the final log of the experiment (`AcceptsLog`) while the claims of
its first message, read through `view` and from the final log, fail is at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

with `N = Q + 2 * ((rounds + 2) + verifierQueries)`. The final log holds the
queries of the verification of the second attempt as well. The hypotheses are
those of `soundness_grind_view_of_accepts`. -/
theorem soundness_grind_view₂_first {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs₁ msgs₂ : A → ℕ → M)
    (proofOf₁ proofOf₂ : A → Proof F D P.batches P.queries) :
    prob (fun res l => P.AcceptsLog bits view (proofOf₁ res.1) (msgs₁ res.1) l ∧
        ClaimsFail P.ldt P.shift θ (P.claims (view (msgs₁ res.1 0)) (committedRow l)))
      (P.experimentGrindView₂ bits view adv msgs₁ msgs₂ proofOf₁ proofOf₂) [] ≤
      (Q + 2 * ((P.rounds + 2) + P.verifierQueries)) * εmax +
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + 2 * ((P.rounds + 2) + P.verifierQueries)) *
          (Q + 2 * ((P.rounds + 2) + P.verifierQueries) - 1) / (2 * Fintype.card D) := by
  have h := P.soundness_grind_view_bind bits view hθ hmca hstep hα hβ hq hadv msgs₁ proofOf₁
    (rest := fun res => (derive _ (msgs₂ res.1) (P.rounds + 2)).bind fun t =>
      (P.verifyGrindView bits view (proofOf₂ res.1) t).bind fun b => .pure (res.1, res.2, b))
    (R := (P.rounds + 2) + P.verifierQueries)
    (fun res => (queryBound_derive (msgs₂ res.1) (P.rounds + 2)).bind fun _ =>
      (P.queryBound_verifyGrindView bits view _ _).bind (m := 0) fun _ => queryBound_pure _ _)
    (E := fun res l => P.AcceptsLog bits view (proofOf₁ res.1) (msgs₁ res.1) l ∧
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs₁ res.1 0)) (committedRow l)))
    fun res l b l' _ hrest hb => by
      obtain ⟨t, l₁, -, hrest⟩ := outcome_bind.mp hrest
      obtain ⟨b₂, l₂, -, hpure⟩ := outcome_bind.mp hrest
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      exact hb
  have hN : (Q + (P.rounds + 2) + P.verifierQueries + ((P.rounds + 2 + P.verifierQueries : ℕ) : ℝ)
      : ℝ) = Q + 2 * ((P.rounds + 2) + P.verifierQueries) := by
    push_cast
    ring
  rwa [hN] at h

/-- **Soundness for the second of two attempts.** In the experiment
`experimentGrindView₂`, with an adversary that makes at most `Q` oracle
queries: the probability that the model verifier accepts the second attempt on
the final log of the experiment (`AcceptsLog`) while the claims of its first
message, read through `view` and from the final log, fail is at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

with `N = Q + 2 * ((rounds + 2) + verifierQueries)`. The hypotheses are those
of `soundness_grind_view_of_accepts`. -/
theorem soundness_grind_view₂_second {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs₁ msgs₂ : A → ℕ → M)
    (proofOf₁ proofOf₂ : A → Proof F D P.batches P.queries) :
    prob (fun res l => P.AcceptsLog bits view (proofOf₂ res.1) (msgs₂ res.1) l ∧
        ClaimsFail P.ldt P.shift θ (P.claims (view (msgs₂ res.1 0)) (committedRow l)))
      (P.experimentGrindView₂ bits view adv msgs₁ msgs₂ proofOf₁ proofOf₂) [] ≤
      (Q + 2 * ((P.rounds + 2) + P.verifierQueries)) * εmax +
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + 2 * ((P.rounds + 2) + P.verifierQueries)) *
          (Q + 2 * ((P.rounds + 2) + P.verifierQueries) - 1) / (2 * Fintype.card D) := by
  have h := P.soundness_grind_view_bind bits view hθ hmca hstep hα hβ hq
    (P.queryBound_experimentGrindView bits view hadv msgs₁ proofOf₁)
    (fun res => msgs₂ res.1) (fun res => proofOf₂ res.1)
    (rest := fun res => .pure (res.1.1, res.1.2, res.2)) (R := 0)
    (fun _ => queryBound_pure _ _)
    (E := fun res l => P.AcceptsLog bits view (proofOf₂ res.1) (msgs₂ res.1) l ∧
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs₂ res.1 0)) (committedRow l)))
    fun res l b l' _ hrest hb => by
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hrest
      exact hb
  have hN : (((Q + (P.rounds + 2) + P.verifierQueries : ℕ) : ℝ) + (P.rounds + 2) +
      P.verifierQueries + ((0 : ℕ) : ℝ) : ℝ) = Q + 2 * ((P.rounds + 2) + P.verifierQueries) := by
    push_cast
    ring
  rw [P.experimentGrindView₂_eq_bind]
  rwa [hN] at h

/-- **Soundness with proof of work for two attempts, on raw messages.**

*Statement.* Whatever the adversary, as long as it makes at most `Q` oracle
queries: in the experiment `experimentGrindView₂`, the probability that for one
of its two attempts the model verifier accepts on the final log of the
experiment (`AcceptsLog`) while the claims of the first message of that
attempt, read through `view` and from the final log, fail is at most

    2 * (N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|)),

with `N = Q + 2 * ((rounds + 2) + verifierQueries)`, the number of oracle
queries of the experiment.

*The final log.* Both events are about the log after both verifications: the
functions the claims are about are read from the hash queries of that log
(`Oracle.committedRow`), for both attempts.

*Hypotheses.* Those of `soundness_grind_view`: `hmca` is the batching
hypothesis and `hstep` the folding hypothesis at agreement `θ`, and by `hα`,
`hβ`, `hq` the number `εmax` bounds the error of every round divided by
`2 ^ bits i`. -/
theorem soundness_grind_view₂ {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs₁ msgs₂ : A → ℕ → M)
    (proofOf₁ proofOf₂ : A → Proof F D P.batches P.queries) :
    prob (fun res l =>
        (P.AcceptsLog bits view (proofOf₁ res.1) (msgs₁ res.1) l ∧
          ClaimsFail P.ldt P.shift θ (P.claims (view (msgs₁ res.1 0)) (committedRow l))) ∨
        (P.AcceptsLog bits view (proofOf₂ res.1) (msgs₂ res.1) l ∧
          ClaimsFail P.ldt P.shift θ (P.claims (view (msgs₂ res.1 0)) (committedRow l))))
      (P.experimentGrindView₂ bits view adv msgs₁ msgs₂ proofOf₁ proofOf₂) [] ≤
      2 * ((Q + 2 * ((P.rounds + 2) + P.verifierQueries)) * εmax +
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + 2 * ((P.rounds + 2) + P.verifierQueries)) *
          (Q + 2 * ((P.rounds + 2) + P.verifierQueries) - 1) / (2 * Fintype.card D)) := by
  rw [two_mul]
  exact (prob_or_le _ _ _ _).trans (add_le_add
    (P.soundness_grind_view₂_first bits view hθ hmca hstep hα hβ hq hadv msgs₁ msgs₂ proofOf₁
      proofOf₂)
    (P.soundness_grind_view₂_second bits view hθ hmca hstep hα hβ hq hadv msgs₁ msgs₂ proofOf₁
      proofOf₂))

end Params

end CertiFri.Compiled
