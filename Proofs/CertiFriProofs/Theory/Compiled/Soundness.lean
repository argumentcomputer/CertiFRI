import CertiFriProofs.Theory.Compiled.SoundnessView

/-!
# Soundness of the compiled protocol in the random-oracle model

The non-interactive protocol: the prover commits with Merkle trees, the
challenges are derived from the transcript (Fiat–Shamir), and the verifier is
the model verifier of `Compiled/Verifier.lean`. The Merkle hash functions and
the challenger are one random oracle.

## The experiment

`Params.experiment adv msgs proofOf`:

1. The adversary `adv` runs with access to the oracle and returns `a`. Its
   prover messages are `msgs a 0, …, msgs a (rounds + 1)` and its proof data
   is `proofOf a`.
2. The verifier derives the challenge of each round as the oracle's answer to
   the transcript so far (messages and challenges) and the message of the
   round (`Oracle.fsExperiment`).
3. The verifier runs `Params.verify` on the proof data and the transcript.

The result is `a` and the verifier's verdict. `Params.experimentGrind` is the
same with a proof-of-work sample in front of every challenge and the verifier
`Params.verifyGrind`.

`Compiled/SoundnessView.lean` has the experiment with proof of work for prover
messages of an arbitrary type, each read as a `Msg` through a function
(`Params.experimentGrindView`). `experimentGrind` is the case where a message
is read as it is.

## Results

* `Params.soundness`: the verifier accepts while the claims fail with
  probability at most
  `N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|)`,
  where `N = Q + (rounds + 2) + P.verifierQueries` counts the oracle queries of
  the adversary, of the derivation of the challenges and of the verifier, and
  `εmax` bounds the round-by-round error of every round.
* `Params.soundness_grind`: the same with proof of work, where the error of
  round `i` is divided by `2 ^ bits i`.
* `Params.soundness_of_relDist`: `Params.soundness` at `θ = 1 - δ` with the
  folding hypothesis proved, in Plonky3's parameters, under
  `4 * δ + (1 / 2) ^ logBlowup ≤ 1`. Only the batching hypothesis remains.
  `Compiled/SoundnessUD.lean` reaches `2 * δ + (1 / 2) ^ logBlowup ≤ 1` with
  neither hypothesis.

`soundness_grind` is the case `view := id` of `Params.soundness_grind_view`
(`Compiled/SoundnessView.lean`), which is proved first. That file also has the
bound for any event that holds only when the model verifier accepted
(`Params.soundness_grind_view_of_imp`).

## Assumptions

They are listed at `Params.soundness`. In short: the random-oracle model with
chained challenges, the proximity hypotheses `CurveMCA` (batching) and
`StepMCA` (folding) as in `PcsRbr.rbrSound`, and the modelling choices of
`Compiled/Read.lean` and `Compiled/Verifier.lean`.

## Not covered

* The executable verifier. The theorems are about the model verifier; that the
  executable verifier accepts only when the model verifier does is a separate
  refinement, to be combined with `Params.soundness_grind_view_of_imp`
  (`Compiled/SoundnessView.lean`).
* Completeness, zero knowledge, and knowledge soundness beyond what the
  conclusion says: the committed functions are read off the oracle queries of
  the run, and the theorem bounds the probability that the verifier accepts
  claims that fail for them.
* A concrete hash function or sponge. Digests and challenges are uniform and
  independent answers of one oracle.
-/

namespace CertiFri.Compiled

open Oracle OracleComp
open PcsRbr (Chal claimsOf ClaimsFail GrindChal roundError)

/-- If `εmax` bounds the error of the batching round, of every folding round
and of the query round, it bounds every round error. -/
theorem roundError_le {R : ℕ} {εα εβ : ℕ → ℝ} {θ : ℝ} {q : ℕ} {εmax : ℝ}
    (hα : ∑ j ∈ Finset.range (R + 1), εα j ≤ εmax) (hβ : ∀ i < R, εβ i ≤ εmax)
    (hq : θ ^ q ≤ εmax) (i : ℕ) : roundError R εα εβ θ q i ≤ εmax := by
  rcases i with _ | k
  · exact hα
  · by_cases hk : k < R
    · rw [PcsRbr.roundError_succ_of_lt hk]
      exact hβ k hk
    · rw [PcsRbr.roundError_succ_of_not_lt hk]
      exact hq

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

namespace Params

variable (P : Params F)

/-! ## The experiments -/

/-- **The soundness experiment.** The adversary runs and returns `a`; the
verifier derives the challenges for the messages `msgs a` along the
Fiat–Shamir chain, and then checks the proof data `proofOf a` against the
transcript. The result is `a` and whether the verifier accepted. -/
def experiment {A : Type*}
    (adv : OracleComp (MerkleAnswer (Msg F D P.batches) (Chal P.ldt P.queries) F D) A)
    (msgs : A → ℕ → Msg F D P.batches) (proofOf : A → Proof F D P.batches P.queries) :
    OracleComp (MerkleAnswer (Msg F D P.batches) (Chal P.ldt P.queries) F D) (A × Bool) :=
  (fsExperiment (P.rounds + 2) adv msgs).bind fun out =>
    (P.verify (proofOf out.1) out.2).bind fun b => .pure (out.1, b)

/-- **The soundness experiment with proof of work.** As `experiment`, but the
oracle's answer to a challenge query of round `i` is a proof-of-work sample of
`bits i` bits together with the challenge, and the verifier is `verifyGrind`. -/
def experimentGrind (bits : ℕ → ℕ) {A : Type*}
    (adv : OracleComp
      (MerkleAnswer (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) F D) A)
    (msgs : A → ℕ → Msg F D P.batches) (proofOf : A → Proof F D P.batches P.queries) :
    OracleComp (MerkleAnswer (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) F D)
      (A × Bool) :=
  (fsExperiment (P.rounds + 2) adv msgs).bind fun out =>
    (P.verifyGrind bits (proofOf out.1) out.2).bind fun b => .pure (out.1, b)

/-! ## Soundness -/

/-- **Soundness of the compiled protocol in the random-oracle model.**

*Statement.* Whatever the adversary, as long as it makes at most `Q` oracle
queries: the probability that the model verifier accepts while the claims of
the adversary's first message fail is at most

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

with `N = Q + (rounds + 2) + P.verifierQueries`, the number of oracle queries
of the whole experiment. The first term is the Fiat–Shamir loss: each query can
be the one that turns a doomed transcript into one that is not, with
probability at most `εmax`. The second term bounds the probability that a hash
answer equals a digest that is already in play (a root of a message, an input
or an answer of an earlier hash query), which is what a prover needs to open a
Merkle root in two ways or to extend a tree after its root was sent.

*What "the claims fail" means.* The first message holds one root per input
batch, and for every claim an opening point `z` and a value `y`. Against the
final log `l` of the run, claim `k` of level `j` is about the function
`(P.claims (msgs a 0) (committedRow l) j k).f` on the coset `shift * H_j`: its
value at the point of the index `i` is the entry of the claimed column in the
row `i` that the hash queries of `l` open under the root of the batch, and zero
if they open none. (If they open two different rows there, which takes a
collision of the hash oracle, it is one of them.)
`ClaimsFail P.ldt P.shift θ claims` says that at some level `j ≤ rounds` there
is no set `B` of at least `θ * |H_j|` points of the coset on which, for every
claim of the level, the function agrees, except possibly at `z`, with a
polynomial of degree at most `2 ^ (rounds - j) * finalDegree` whose value at
`z` is `y`. So outside the event of the theorem, an accepted proof has claims
that hold in this sense, at every level, for the functions the oracle queries
of the run determine.

*Assumptions.*

* `0 ≤ θ`. The agreement `θ` is a parameter of the statement: a larger `θ`
  makes "the claims fail" a weaker condition and the theorem stronger, at the
  price of the larger query error `θ ^ queries`.
* The random-oracle model. The leaf hash, the two-to-one compression and the
  challenger are one oracle with three disjoint kinds of queries, each
  answered uniformly and independently: a digest in `D` for a hash query, a
  challenge of the round for a challenge query. `Q` counts the adversary's
  queries of all kinds. There is no bound on the adversary's computation.
* Chained challenges. The challenge of a round is the answer to the query
  made of the whole transcript so far, earlier challenges included, and the
  message of the round. The batching challenge `α` and the folding challenges
  are uniform in `F`, the challenge of the query round is `queries` uniform
  points of the first domain, which is the same as `queries` uniform indices
  below `2 ^ n`.
* `hmca`, the batching hypothesis: mutual correlated agreement for curves
  (`CurveMCA`) on the coset of every level `j ≤ rounds`, for as many terms as
  the level has claims, at agreement `θ`, with error `εα j`.
* `hstep`, the folding hypothesis: `StepMCA` for every folding round, at
  agreement `θ`, with error `εβ i`.
* `hα`, `hβ`, `hq`: `εmax` bounds the error of every round, that is
  `∑ j ≤ rounds, εα j` for the batching round, `εβ i` for folding round `i`,
  and `θ ^ queries` for the query round.
* The parameters satisfy the fields of `Params`: `ω` is a primitive `2 ^ n`-th
  root of unity, `rounds ≤ n`, the shift is not zero, no input matrix is taller
  than `2 ^ n`, and a claim of level `j` names a column of a matrix of
  log-height `n - j`.

*Modelling choices.* The verifier is the model verifier `Params.verify`
(`Compiled/Verifier.lean` lists the checks of Plonky3 it leaves out). All rows
hold elements of the one field `F`. The first message holds the input roots
together with the opening points and the claimed values, so the adversary
chooses all three before `α` is derived. The final polynomial is the list of
its first `finalDegree` coefficients. The degree bound in "the claims fail" is
one more than the degree of an honest polynomial, and the agreement is not
asked at the opening point of a claim (see `Theory/PcsRbr/Claims.lean`). -/
theorem soundness {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : ∑ j ∈ Finset.range (P.rounds + 1), εα j ≤ εmax) (hβ : ∀ i < P.rounds, εβ i ≤ εmax)
    (hq : θ ^ P.queries ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer (Msg F D P.batches) (Chal P.ldt P.queries) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → Msg F D P.batches)
    (proofOf : A → Proof F D P.batches P.queries) :
    prob (fun res l => res.2 = true ∧
        ClaimsFail P.ldt P.shift θ (P.claims (msgs res.1 0) (committedRow l)))
      (P.experiment adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have : ∀ i, Nonempty (Chal P.ldt P.queries i) :=
    PcsRbr.Chal.nonempty P.domain_zero_nonempty P.queries
  have hnd : ∀ t : Transcript (PcsRbr.Msg F P.numClaims) (Chal P.ldt P.queries) (P.rounds + 2),
      ClaimsFail P.ldt P.shift θ (claimsOf t) → PcsRbr.Accepts P.ldt P.shift t →
        ¬ PcsRbr.doomed P.ldt P.shift θ P.queries (P.rounds + 2) t := fun t =>
    PcsRbr.not_doomed_of_accepts t
  have h := prob_fsExperiment_bind_committedRow_le (r := P.rounds + 2)
    (PcsRbr.rbrSound P.ldt P.shift_ne hθ P.queries hmca hstep)
    (fun i _ => roundError_le hα hβ hq i) ((pow_nonneg hθ _).trans hq)
    (PcsRbr.doomed_zero P.ldt P.shift θ P.queries _)
    (digestsOf := digestsOfAt P.rounds) (M := P.batches + P.rounds)
    (fun x => length_chalDigests_le P.rounds id x)
    (read := fun j m c => P.read j m c) (fun j m c c' hc => P.read_congr j m c c' hc)
    hadv msgs
    (rest := fun out => (P.verify (proofOf out.1) out.2).bind fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (P.queryBound_verify _ _).bind (m := 0) fun _ => queryBound_pure _ _)
    (E := fun res l => res.2 = true ∧
      ClaimsFail P.ldt P.shift θ (P.claims (msgs res.1 0) (committedRow l)))
    (fun out l res l' hexp hrun hE hno => by
      obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      obtain ⟨hb, hfail⟩ := hE
      have hb' : b = true := hb
      subst hb'
      refine hnd _ ?_ (P.accepts_of_outcome_verify hver hno)
      have h0 : out.2.msgs[0]? = some (msgs out.1 0) := by
        rw [msgs_of_outcome_fsExperiment hexp, List.getElem?_map,
          List.getElem?_range (Nat.succ_pos _)]
        rfl
      rw [PcsRbr.claimsOf_mapIdx _ out.2 h0]
      exact hfail)
  rwa [show ((P.rounds + 2 : ℕ) : ℝ) = (P.rounds : ℝ) + 2 by push_cast; rfl] at h

/-- **Soundness with proof of work.** The setting of `soundness`, with a
proof-of-work check of `bits i` bits in round `i`: the oracle's answer to the
challenge query of round `i` holds `bits i` uniform bits beside the challenge,
and the verifier (`verifyGrind`) rejects unless all bits of all rounds are
zero. The bound is that of `soundness` with the error of every round divided
by `2 ^ bits i`: `εmax` has to bound `(∑ j ≤ rounds, εα j) / 2 ^ bits 0`,
`εβ i / 2 ^ bits (i + 1)` for folding round `i`, and
`θ ^ queries / 2 ^ bits (rounds + 1)`.

In Plonky3 `bits 0 = 0`, `bits (i + 1) = commit_proof_of_work_bits` for
`i < rounds`, and `bits (rounds + 1) = query_proof_of_work_bits`. The sampled
bits are uniform and independent of the challenge here, as two parts of one
answer of the oracle; `Theory/PcsRbr/Grinding.lean` says how this differs from
Plonky3's challenger. The other assumptions are those of `soundness`. -/
theorem soundness_grind (bits : ℕ → ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j))
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), εα j) / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp
      (MerkleAnswer (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) F D) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (msgs : A → ℕ → Msg F D P.batches)
    (proofOf : A → Proof F D P.batches P.queries) :
    prob (fun res l => res.2 = true ∧
        ClaimsFail P.ldt P.shift θ (P.claims (msgs res.1 0) (committedRow l)))
      (P.experimentGrind bits adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) :=
  P.soundness_grind_view bits id hθ hmca hstep hα hβ hq hadv msgs proofOf

/-! ## The folding hypothesis proved -/

/-- **Soundness with the folding hypothesis proved.** In Plonky3's parameters,
`n = rounds + logBlowup + logFinalPolyLen` and `finalDegree = 2 ^ logFinalPolyLen`,
so that every level has rate `2 ^ (-logBlowup)`. Let `δ ≥ 0` with
`4 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then `soundness` holds at agreement
`θ = 1 - δ` with no hypothesis on the folding rounds: `StepMCA` is proved by
`stepMCA_of_relDist`, with the error `2 * (δ * 2 ^ (n - i - 1) + 1) / |F|` in
round `i`, of which `2 * (δ * 2 ^ (n - 1) + 1) / |F|` is the largest.

The batching hypothesis `hmca` remains, and so do the other assumptions of
`soundness`. The radius is small: `δ ≤ (1 - 2 ^ (-logBlowup)) / 4`, so each
query contributes a factor `1 - δ > 3 / 4`. -/
theorem soundness_of_relDist {logBlowup logFinalPolyLen : ℕ}
    (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 4 * δ + (1 / 2) ^ logBlowup ≤ 1) {εα : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) (1 - δ) (εα j))
    (hα : ∑ j ∈ Finset.range (P.rounds + 1), εα j ≤ εmax)
    (hβ : 2 * (δ * 2 ^ (P.n - 1) + 1) / Fintype.card F ≤ εmax)
    (hq : (1 - δ) ^ P.queries ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer (Msg F D P.batches) (Chal P.ldt P.queries) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → Msg F D P.batches)
    (proofOf : A → Proof F D P.batches P.queries) :
    prob (fun res l => res.2 = true ∧
        ClaimsFail P.ldt P.shift (1 - δ) (P.claims (msgs res.1 0) (committedRow l)))
      (P.experiment adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) logBlowup
    linarith
  exact P.soundness hθ hmca (fun i hi => P.stepMCA_of_rate hn hfinal hδ hrate hi) hα
    (fun i hi => (P.stepError_le hδ hi).trans hβ) hq hadv msgs proofOf

end Params

end CertiFri.Compiled
