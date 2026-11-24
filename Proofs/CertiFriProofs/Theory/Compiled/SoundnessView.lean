import CertiFriProofs.Theory.Compiled.Accepts
import CertiFriProofs.Theory.Unconditional

/-!
# Soundness of the compiled protocol for raw messages

The soundness theorems of the compiled protocol with proof of work, in the
form where the prover messages are of an arbitrary type.

In `Compiled/Read.lean` a prover message is a record `Msg F D P.batches`. A
verifier may absorb another encoding of a message into its challenger, for
instance a list of observations. Here the adversary's messages, and with them
the messages of the challenge queries of the random oracle, are of any type `M`
with decidable equality, and a function `view : M → Msg F D P.batches` says how
a raw message is read. Nothing is assumed about `view`: two raw messages with
the same reading are different queries to the oracle.

## The experiment

`Params.experimentGrindView bits view adv msgs proofOf`:

1. The adversary `adv` runs with access to the oracle and returns `a`. Its
   raw messages are `msgs a 0, …, msgs a (rounds + 1)` and its proof data is
   `proofOf a`.
2. The challenge of each round is derived as the oracle's answer to the
   transcript so far (raw messages and challenges) and the raw message of the
   round (`Oracle.fsExperiment`). The answer holds `bits i` proof-of-work bits
   beside the challenge of round `i`.
3. The model verifier `Params.verifyGrindView` runs on the proof data and the
   transcript, reading every message through `view`.

## Results

Each bounds a probability by

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

where `N` is the number of oracle queries of the whole experiment and `εmax`
bounds the error of every round, divided by `2 ^ bits i` in round `i`.

* `Params.soundness_grind_view`: the model verifier accepts while the claims of
  the first message, read through `view`, fail.
* `Params.soundness_grind_view_of_imp`: the same for any event of the
  adversary's output and the final log that holds only when the model verifier
  accepted. This is the form for another verifier that accepts only when the
  model verifier does.
* `Params.soundness_grind_view_of_accepts`: the statement behind both, for any
  computation after the derivation of the challenges and any event of it that,
  in a final log without a hit, implies that the claims fail, that the
  proof-of-work checks pass, and that the transcript read from the final log
  is accepted in the oracle model.
* `Params.soundness_grind_view_of_relDist` and
  `Params.soundness_grind_view_of_imp_of_relDist`: the first two at agreement
  `θ = 1 - δ` with the folding hypothesis proved, in Plonky3's parameters,
  under `4 * δ + (1 / 2) ^ logBlowup ≤ 1` (`Params.stepMCA_of_rate`).

To state the hypothesis `hE` of `soundness_grind_view_of_imp` for a verifier
that is a function of the answers of the oracle:

* `Params.run_verifyGrindView_of_outcome`: the verdict of the model verifier in
  the experiment is its result against the final log completed to a function
  (`Log.toFun`), on the transcript that function gives along the Fiat–Shamir
  chain (`Oracle.fsTranscript`).

Also here: the transcript of the Fiat–Shamir experiment holds the adversary's
messages (`msgs_of_outcome_fsExperiment`), and it is the transcript any later
log gives along the chain (`eq_fsTranscript_of_outcome_fsExperiment`).

## Assumptions

Those of `Params.soundness` and `Params.soundness_grind`
(`Compiled/Soundness.lean`), where they are listed: the random-oracle model
with chained challenges, the proximity hypotheses `CurveMCA` (batching) and
`StepMCA` (folding), and the modelling choices of `Compiled/Read.lean` and
`Compiled/Verifier.lean`.

## Not covered

* A verifier other than the model verifier. That it accepts only when the model
  verifier does is the hypothesis `hE` of `Params.soundness_grind_view_of_imp`.
* The protocol without proof of work on raw messages. It is the case
  `bits := fun _ => 0`, up to the trivial proof-of-work component of a
  challenge.
* Completeness and zero knowledge.
-/

namespace CertiFri.Compiled

open Oracle OracleComp
open PcsRbr (Chal claimsOf ClaimsFail Accepts GrindChal PowPasses ungrind roundError)

/-! ## The messages of the experiment's transcript -/

section Messages

universe u v u' w

variable {M : Type u} {C : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}
  [DecidableEq (FSQuery M C X')]

/-- The transcript the verifier derives holds the messages it was given. -/
theorem msgs_of_outcome_derive {ms : ℕ → M} :
    ∀ {i : ℕ} {l l' : Log (FSAnswer (Msg := M) C Y')} {t : Transcript M C i},
      Outcome (derive Y' ms i) l t l' → t.msgs = (List.range i).map ms
  | 0, _, _, _, h => by
    obtain ⟨rfl, _⟩ := h
    rfl
  | i + 1, l, l', t, h => by
    rw [derive, outcome_bind] at h
    obtain ⟨t₀, l₁, h₀, h⟩ := h
    obtain ⟨c, l₂, hc, rfl, rfl⟩ := outcome_queryBind.mp h
    rw [List.range_succ, List.map_append, List.map_singleton, ← msgs_of_outcome_derive h₀]
    rfl

/-- The transcript of the Fiat–Shamir experiment holds the adversary's
messages. -/
theorem msgs_of_outcome_fsExperiment {α : Type w} {r : ℕ}
    {adv : OracleComp (FSAnswer (Msg := M) C Y') α} {msgs : α → ℕ → M}
    {l l' : Log (FSAnswer (Msg := M) C Y')} {out : α × Transcript M C r}
    (h : Outcome (fsExperiment r adv msgs) l out l') :
    out.2.msgs = (List.range r).map (msgs out.1) := by
  obtain ⟨l₁, -, hd⟩ := outcome_fsExperiment.mp h
  exact msgs_of_outcome_derive hd

/-- The transcript of the Fiat–Shamir experiment is the transcript that any
later log, completed to a function, gives along the chain. -/
theorem eq_fsTranscript_of_outcome_fsExperiment {α : Type w} {r : ℕ}
    {adv : OracleComp (FSAnswer (Msg := M) C Y') α} {msgs : α → ℕ → M}
    {l₀ l l' : Log (FSAnswer (Msg := M) C Y')} {out : α × Transcript M C r}
    (h : Outcome (fsExperiment r adv msgs) l₀ out l) (hl : l <+: l')
    (f : ∀ x : FSQuery M C X', FSAnswer C Y' x) :
    out.2 = fsTranscript (l'.toFun f) (msgs out.1) r := by
  obtain ⟨l₁, -, hd⟩ := outcome_fsExperiment.mp h
  exact hd.eq_fsTranscript fun x y hxy => Log.toFun_of_dlookup f (dlookup_of_prefix hxy hl)

omit [DecidableEq (FSQuery M C X')] in
/-- Dropping the proof-of-work samples keeps the messages. -/
theorem msgs_ungrind {bits : ℕ → ℕ} :
    ∀ {i : ℕ} (t : Transcript M (GrindChal bits C) i), (ungrind t).msgs = t.msgs
  | _, .nil => rfl
  | _, .snoc t m c => by
    rw [PcsRbr.ungrind_snoc, Transcript.msgs_snoc, Transcript.msgs_snoc, msgs_ungrind t]

end Messages

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

namespace Params

variable (P : Params F)

/-! ## The experiment -/

/-- **The soundness experiment with proof of work, on raw messages.** The
adversary runs and returns `a`; its messages `msgs a` are of a type `M`. The
challenges are derived along the Fiat–Shamir chain: the oracle's answer to the
challenge query of round `i`, which holds the raw messages and the answers so
far, is a proof-of-work sample of `bits i` bits together with the challenge.
Then the model verifier `verifyGrindView`, which reads a raw message through
`view`, checks the proof data `proofOf a` against the transcript. The result is
`a` and whether the verifier accepted. -/
def experimentGrindView {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {A : Type*}
    (adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A)
    (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries) :
    OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) (A × Bool) :=
  (fsExperiment (P.rounds + 2) adv msgs).bind fun out =>
    (P.verifyGrindView bits view (proofOf out.1) out.2).bind fun b => .pure (out.1, b)

omit [Fintype F] [Fintype D] [Nonempty D] in
/-- **The verdict of the model verifier in the experiment, as a function of
the final log.** After the adversary and the derivation of the challenges, let
the model verifier return `b` and leave the log `l'`. Complete `l'` to a
function with any `f`. Then `b` is the result of the model verifier against
that function, on the transcript that function gives along the Fiat–Shamir
chain for the adversary's messages. -/
theorem run_verifyGrindView_of_outcome {M : Type} [DecidableEq M] {bits : ℕ → ℕ}
    {view : M → Msg F D P.batches} {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A}
    {msgs : A → ℕ → M} {pf : Proof F D P.batches P.queries}
    {out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)}
    {l₀ l l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)} {b : Bool}
    (hexp : Outcome (fsExperiment (P.rounds + 2) adv msgs) l₀ out l)
    (hver : Outcome (P.verifyGrindView bits view pf out.2) l b l')
    (f : ∀ x, MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D x) :
    (P.verifyGrindView bits view pf
      (fsTranscript (l'.toFun f) (msgs out.1) (P.rounds + 2))).run (l'.toFun f) = b := by
  rw [← eq_fsTranscript_of_outcome_fsExperiment hexp hver.prefix f]
  exact hver.run_toFun f

/-! ## Soundness with proof of work, on raw messages -/

/-- **Soundness with proof of work for any verifier that accepts only what the
oracle-model protocol accepts.** The adversary makes at most `Q` oracle
queries and outputs raw messages of a type `M`, read through `view`. The
challenges are derived as in `experimentGrindView`, and then any computation
`rest` runs, with at most `R` oracle queries. Let `E` be an event of its result
and the final log such that, on every outcome whose final log `l'` has no hit,
`E` implies three things: the claims of the adversary's first message, read
from `l'`, fail; every proof-of-work sample of the transcript is zero; and the
transcript without the samples, read through `view` and from the rows `l'`
commits to, is accepted by the oracle-model protocol. Then `E` has probability
at most

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

with `N = Q + (rounds + 2) + R`.

A hit (`Oracle.Hit`) is a hash answer equal to a digest that is already in
play: a root of a message, read through `view`, or an input or an answer of an
earlier hash query. The second term of the bound is the probability of one.

The hypotheses are those of `Params.soundness_grind`
(`Compiled/Soundness.lean`): `hmca` is the batching hypothesis, `hstep` the
folding hypothesis, and by `hα`, `hβ`, `hq` the number `εmax` bounds the error
of every round divided by `2 ^ bits i`. -/
theorem soundness_grind_view_of_accepts {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*} {B : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M)
    {rest : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2) →
      OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) B} {R : ℕ}
    (hrest : ∀ out, (rest out).QueryBound R)
    {E : B → Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) → Prop}
    (hE : ∀ (out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2))
      (l : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)) (b : B)
      (l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l → Outcome (rest out) l b l' →
      E b l' → ¬ HasBad (Hit (fun j m => digestsOfAt P.rounds j (view m)) (P.rounds + 2)) l' →
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs out.1 0)) (committedRow l')) ∧
        PowPasses out.2 ∧
        Accepts P.ldt P.shift
          ((ungrind out.2).mapIdx fun j m => P.read j (view m) (committedRow l'))) :
    prob E ((fsExperiment (P.rounds + 2) adv msgs).bind rest) [] ≤
      (Q + (P.rounds + 2) + R) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + R) ^ 2 /
          (4 * Fintype.card D) := by
  have : ∀ i, Nonempty (Chal P.ldt P.queries i) :=
    PcsRbr.Chal.nonempty P.domain_zero_nonempty P.queries
  have hε : ∀ i < P.rounds + 2, roundError P.rounds εα εβ θ P.queries i / 2 ^ bits i ≤ εmax := by
    intro i hi
    rcases i with _ | k
    · exact hα
    · by_cases hk : k < P.rounds
      · rw [PcsRbr.roundError_succ_of_lt hk]
        exact hβ k hk
      · obtain rfl : k = P.rounds := by omega
        rw [PcsRbr.roundError_last]
        exact hq
  have hnd : ∀ t : Transcript (PcsRbr.Msg F P.numClaims) (GrindChal bits (Chal P.ldt P.queries))
      (P.rounds + 2), PowPasses t → ClaimsFail P.ldt P.shift θ (claimsOf (ungrind t)) →
        Accepts P.ldt P.shift (ungrind t) →
          ¬ PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) (P.rounds + 2) t :=
    fun t => PcsRbr.not_grindDoomed_of_accepts t
  have h := prob_fsExperiment_bind_committedRow_le (r := P.rounds + 2)
    (PcsRbr.rbrSound_grind P.ldt P.shift_ne hθ P.queries hmca hstep bits) hε
    ((div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq)
    (PcsRbr.grindDoomed_nil (PcsRbr.doomed_zero P.ldt P.shift θ P.queries _))
    (digestsOf := fun j m => digestsOfAt P.rounds j (view m)) (M := P.batches + P.rounds)
    (fun x => length_chalDigests_le P.rounds view x)
    (read := fun j m c => P.read j (view m) c)
    (fun j m c c' hc => P.read_congr j (view m) c c' hc)
    hadv msgs hrest (E := E)
    (fun out l b l' hexp hrun hb hno => by
      obtain ⟨hfail, hpow, hacc⟩ := hE out l b l' hexp hrun hb hno
      refine hnd _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow) ?_ ?_
      · have h0 : (ungrind out.2).msgs[0]? = some (msgs out.1 0) := by
          rw [msgs_ungrind, msgs_of_outcome_fsExperiment hexp, List.getElem?_map,
            List.getElem?_range (Nat.succ_pos _)]
          rfl
        rw [PcsRbr.ungrind_mapIdx, PcsRbr.claimsOf_mapIdx _ (ungrind out.2) h0]
        exact hfail
      · rw [PcsRbr.ungrind_mapIdx]
        exact hacc)
  rwa [show ((P.rounds + 2 : ℕ) : ℝ) = (P.rounds : ℝ) + 2 by push_cast; rfl] at h

/-- **Soundness with proof of work for an event that implies acceptance, on raw
messages.** In the experiment `experimentGrindView`, let `E` be an event of the
adversary's output and the final log that holds only when the model verifier
accepted: on every outcome of the adversary and the derivation of the
challenges, and every outcome of the model verifier after it, if `E` holds of
the final log then the verdict is `true`. Then the probability that `E` holds
while the claims of the adversary's first message, read through `view`, fail
is at most the bound of `soundness_grind_view`. The other hypotheses are those
of `soundness_grind_view`.

This is the form for another verifier whose verdict is a function of the
adversary's output and the answers of the oracle: its acceptance is `E`, and
`hE` is the statement that it accepts only when the model verifier does. For
an event of the final log completed to a function, `hE` follows from
`run_verifyGrindView_of_outcome`. -/
theorem soundness_grind_view_of_imp {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries)
    (E : A → Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) → Prop)
    (hE : ∀ (out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2))
      (l : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)) (b : Bool)
      (l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l →
      Outcome (P.verifyGrindView bits view (proofOf out.1) out.2) l b l' →
      E out.1 l' → b = true) :
    prob (fun res l => E res.1 l ∧
        ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindView bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  refine P.soundness_grind_view_of_accepts bits view hθ hmca hstep hα hβ hq hadv msgs
    (rest := fun out =>
      (P.verifyGrindView bits view (proofOf out.1) out.2).bind fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (P.queryBound_verifyGrindView bits view _ _).bind (m := 0) fun _ =>
      queryBound_pure _ _)
    (E := fun res l => E res.1 l ∧
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
    fun out l res l' hexp hrun hres hno => ?_
  obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
  obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
  obtain rfl : b = true := hE out l b _ hexp hver hres.1
  exact ⟨hres.2, P.accepts_of_outcome_verifyGrindView hver hno⟩

/-- **Soundness with proof of work, on raw messages.**

*Statement.* Whatever the adversary, as long as it makes at most `Q` oracle
queries: in the experiment `experimentGrindView`, the probability that the
model verifier `verifyGrindView` accepts while the claims of the adversary's
first message, read through `view`, fail is at most

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

with `N = Q + (rounds + 2) + P.verifierQueries`.

*Setting.* That of `Params.soundness_grind` (`Compiled/Soundness.lean`), which
is the case `view := id`. The doc comment of `Params.soundness` lists the
assumptions and says what "the claims fail" means. Here the adversary's
messages are of a type `M` with decidable equality, the challenge of a round is
the oracle's answer to the transcript of raw messages and challenges so far and
the raw message of the round, and the verifier and the claims read a raw
message through `view`. Nothing is assumed about `view`.

*Hypotheses.* `hmca` is the batching hypothesis and `hstep` the folding
hypothesis, at agreement `θ`. By `hα`, `hβ`, `hq` the number `εmax` bounds the
error of every round divided by `2 ^ bits i`: `(∑ j ≤ rounds, εα j) / 2 ^ bits 0`
for the batching round, `εβ i / 2 ^ bits (i + 1)` for folding round `i`, and
`θ ^ queries / 2 ^ bits (rounds + 1)` for the query round. -/
theorem soundness_grind_view {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries) :
    prob (fun res l => res.2 = true ∧
        ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindView bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  refine P.soundness_grind_view_of_accepts bits view hθ hmca hstep hα hβ hq hadv msgs
    (rest := fun out =>
      (P.verifyGrindView bits view (proofOf out.1) out.2).bind fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (P.queryBound_verifyGrindView bits view _ _).bind (m := 0) fun _ =>
      queryBound_pure _ _)
    (E := fun res l => res.2 = true ∧
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
    fun out l res l' hexp hrun hres hno => ?_
  obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
  obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
  obtain rfl : b = true := hres.1
  exact ⟨hres.2, P.accepts_of_outcome_verifyGrindView hver hno⟩

/-! ## The folding hypothesis proved -/

/-- **The folding hypothesis in Plonky3's parameters.** Let
`n = rounds + logBlowup + logFinalPolyLen` and `finalDegree = 2 ^ logFinalPolyLen`,
so that every level has rate `2 ^ (-logBlowup)`, and let `δ ≥ 0` with
`4 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then every folding round satisfies `StepMCA`
at agreement `1 - δ`, with the error `2 * (δ * |domain (i + 1)| + 1) / |F|` in
round `i` (`stepMCA_of_relDist`). -/
theorem stepMCA_of_rate {logBlowup logFinalPolyLen : ℕ}
    (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 4 * δ + (1 / 2) ^ logBlowup ≤ 1) {i : ℕ} (hi : i < P.rounds) :
    StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) (1 - δ)
      (2 * (δ * (twoAdicDomain P.ω P.n (i + 1)).card + 1) / Fintype.card F) := by
  refine stepMCA_of_relDist (P.ldt.step i hi) _ hδ ?_
  have h := Compose.twoAdic_relDist hn P.prim hrate (i := i + 1) hi
  rwa [← hfinal] at h

/-- The error of `stepMCA_of_rate` in a folding round is at most
`2 * (δ * 2 ^ (n - 1) + 1) / |F|`, its value in the first round. -/
theorem stepError_le {δ : ℝ} (hδ : 0 ≤ δ) {i : ℕ} (hi : i < P.rounds) :
    2 * (δ * (twoAdicDomain P.ω P.n (i + 1)).card + 1) / Fintype.card F ≤
      2 * (δ * 2 ^ (P.n - 1) + 1) / Fintype.card F := by
  have hcard : ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ 2 ^ (P.n - 1) := by
    rw [card_twoAdicDomain P.prim (by have := P.rounds_le; omega)]
    exact_mod_cast Nat.pow_le_pow_right two_pos (by omega)
  gcongr

/-- **Soundness for an event that implies acceptance, on raw messages, with
the folding hypothesis proved.** `soundness_grind_view_of_imp` at agreement
`θ = 1 - δ`, in Plonky3's parameters: `n = rounds + logBlowup + logFinalPolyLen`
and `finalDegree = 2 ^ logFinalPolyLen`. For `δ ≥ 0` with
`4 * δ + (1 / 2) ^ logBlowup ≤ 1` there is no hypothesis on the folding
rounds (`stepMCA_of_rate`). The error of a folding round is at most
`2 * (δ * 2 ^ (n - 1) + 1) / |F|`, divided by `2 ^ bits (i + 1)` for the proof
of work of round `i`. The batching hypothesis `hmca` remains. -/
theorem soundness_grind_view_of_imp_of_relDist {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {logBlowup logFinalPolyLen : ℕ}
    (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 4 * δ + (1 / 2) ^ logBlowup ≤ 1) {εα : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) (1 - δ) (εα j))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds,
      2 * (δ * 2 ^ (P.n - 1) + 1) / Fintype.card F / 2 ^ bits (i + 1) ≤ εmax)
    (hq : (1 - δ) ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries)
    (E : A → Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) → Prop)
    (hE : ∀ (out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2))
      (l : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)) (b : Bool)
      (l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l →
      Outcome (P.verifyGrindView bits view (proofOf out.1) out.2) l b l' →
      E out.1 l' → b = true) :
    prob (fun res l => E res.1 l ∧
        ClaimsFail P.ldt P.shift (1 - δ) (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindView bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) logBlowup
    linarith
  refine P.soundness_grind_view_of_imp bits view hθ hmca
    (fun i hi => P.stepMCA_of_rate hn hfinal hδ hrate hi) hα (fun i hi => ?_) hq hadv msgs
    proofOf E hE
  exact (div_le_div_of_nonneg_right (P.stepError_le hδ hi) (by positivity)).trans (hβ i hi)

/-- **Soundness with proof of work, on raw messages, with the folding
hypothesis proved.** `soundness_grind_view` at agreement `θ = 1 - δ`, in
Plonky3's parameters: `n = rounds + logBlowup + logFinalPolyLen` and
`finalDegree = 2 ^ logFinalPolyLen`. For `δ ≥ 0` with
`4 * δ + (1 / 2) ^ logBlowup ≤ 1` there is no hypothesis on the folding rounds
(`stepMCA_of_rate`). The error of a folding round is at most
`2 * (δ * 2 ^ (n - 1) + 1) / |F|`, divided by `2 ^ bits (i + 1)` for the proof
of work of round `i`. The batching hypothesis `hmca` remains. -/
theorem soundness_grind_view_of_relDist {M : Type} [DecidableEq M] (bits : ℕ → ℕ)
    (view : M → Msg F D P.batches) {logBlowup logFinalPolyLen : ℕ}
    (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 4 * δ + (1 / 2) ^ logBlowup ≤ 1) {εα : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) (1 - δ) (εα j))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds,
      2 * (δ * 2 ^ (P.n - 1) + 1) / Fintype.card F / 2 ^ bits (i + 1) ≤ εmax)
    (hq : (1 - δ) ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries) :
    prob (fun res l => res.2 = true ∧
        ClaimsFail P.ldt P.shift (1 - δ) (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindView bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) logBlowup
    linarith
  refine P.soundness_grind_view bits view hθ hmca
    (fun i hi => P.stepMCA_of_rate hn hfinal hδ hrate hi) hα (fun i hi => ?_) hq hadv msgs
    proofOf
  exact (div_le_div_of_nonneg_right (P.stepError_le hδ hi) (by positivity)).trans (hβ i hi)

end Params

end CertiFri.Compiled
