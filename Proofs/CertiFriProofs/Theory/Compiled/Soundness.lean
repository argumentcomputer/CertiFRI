import CertiFriProofs.Theory.Compiled.Accepts
import CertiFriProofs.Theory.Unconditional

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

## Results

* `Params.soundness`: the verifier accepts while the claims fail with
  probability at most
  `N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|)`,
  where `N = Q + (rounds + 2) + P.verifierQueries` counts the oracle queries of
  the adversary, of the derivation of the challenges and of the verifier, and
  `εmax` bounds the round-by-round error of every round.
* `Params.soundness_grind`: the same with proof of work, where the error of
  round `i` is divided by `2 ^ bits i`.
* `Params.soundness_of_relDist`: `Params.soundness` at `θ = 1 - δ` with the
  folding hypothesis proved, in Plonky3's parameters, under
  `4 * δ + (1 / 2) ^ logBlowup ≤ 1`. Only the batching hypothesis remains.

## Assumptions

They are listed at `Params.soundness`. In short: the random-oracle model with
chained challenges, the proximity hypotheses `CurveMCA` (batching) and
`StepMCA` (folding) as in `PcsRbr.rbrSound`, and the modelling choices of
`Compiled/Read.lean` and `Compiled/Verifier.lean`.

## Not covered

* The executable verifier. The theorems are about the model verifier; that the
  executable verifier accepts only when the model verifier does is a separate
  refinement.
* Completeness, zero knowledge, and knowledge soundness beyond what the
  conclusion says: the committed functions are read off the oracle queries of
  the run, and the theorem bounds the probability that the verifier accepts
  claims that fail for them.
* A concrete hash function or sponge. Digests and challenges are uniform and
  independent answers of one oracle.
-/

namespace CertiFri.Compiled

open Oracle OracleComp
open PcsRbr (Chal claimsOf ClaimsFail GrindChal PowPasses ungrind roundError)

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

omit [DecidableEq (FSQuery M C X')] in
/-- Dropping the proof-of-work samples keeps the messages. -/
theorem msgs_ungrind {bits : ℕ → ℕ} :
    ∀ {i : ℕ} (t : Transcript M (GrindChal bits C) i), (ungrind t).msgs = t.msgs
  | _, .nil => rfl
  | _, .snoc t m c => by
    rw [PcsRbr.ungrind_snoc, Transcript.msgs_snoc, Transcript.msgs_snoc, msgs_ungrind t]

end Messages

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

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

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
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + (P.rounds + 2) + P.verifierQueries) *
          (Q + (P.rounds + 2) + P.verifierQueries - 1) / (2 * Fintype.card D) := by
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
    (digestsOf := digestsOf) (K := P.batches + 1) (fun m => (length_digestsOf m).le)
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
  push_cast at h
  exact h

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
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + (P.rounds + 2) + P.verifierQueries) *
          (Q + (P.rounds + 2) + P.verifierQueries - 1) / (2 * Fintype.card D) := by
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
        PcsRbr.Accepts P.ldt P.shift (ungrind t) →
          ¬ PcsRbr.grindDoomed bits (PcsRbr.doomed P.ldt P.shift θ P.queries) (P.rounds + 2) t :=
    fun t => PcsRbr.not_grindDoomed_of_accepts t
  have h := prob_fsExperiment_bind_committedRow_le (r := P.rounds + 2)
    (PcsRbr.rbrSound_grind P.ldt P.shift_ne hθ P.queries hmca hstep bits) hε
    ((div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq)
    (PcsRbr.grindDoomed_nil (PcsRbr.doomed_zero P.ldt P.shift θ P.queries _))
    (digestsOf := digestsOf) (K := P.batches + 1) (fun m => (length_digestsOf m).le)
    (read := fun j m c => P.read j m c) (fun j m c c' hc => P.read_congr j m c c' hc)
    hadv msgs
    (rest := fun out => (P.verifyGrind bits (proofOf out.1) out.2).bind fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (P.queryBound_verifyGrind bits _ _).bind (m := 0) fun _ => queryBound_pure _ _)
    (E := fun res l => res.2 = true ∧
      ClaimsFail P.ldt P.shift θ (P.claims (msgs res.1 0) (committedRow l)))
    (fun out l res l' hexp hrun hE hno => by
      obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      obtain ⟨hb, hfail⟩ := hE
      have hb' : b = true := hb
      subst hb'
      obtain ⟨hpow, hacc⟩ := P.accepts_of_outcome_verifyGrind hver hno
      refine hnd _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow) ?_ ?_
      · have h0 : (ungrind out.2).msgs[0]? = some (msgs out.1 0) := by
          rw [msgs_ungrind, msgs_of_outcome_fsExperiment hexp, List.getElem?_map,
            List.getElem?_range (Nat.succ_pos _)]
          rfl
        rw [PcsRbr.ungrind_mapIdx, PcsRbr.claimsOf_mapIdx _ (ungrind out.2) h0]
        exact hfail
      · rw [PcsRbr.ungrind_mapIdx]
        exact hacc)
  push_cast at h
  exact h

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
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + (P.rounds + 2) + P.verifierQueries) *
          (Q + (P.rounds + 2) + P.verifierQueries - 1) / (2 * Fintype.card D) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) logBlowup
    linarith
  refine P.soundness hθ hmca
    (εβ := fun i => 2 * (δ * (twoAdicDomain P.ω P.n (i + 1)).card + 1) / Fintype.card F)
    (fun i hi => stepMCA_of_relDist (P.ldt.step i hi) _ hδ ?_) hα (fun i hi => ?_) hq hadv msgs
    proofOf
  · have h := Compose.twoAdic_relDist hn P.prim hrate (i := i + 1) hi
    rwa [← hfinal] at h
  · have hcard : ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ 2 ^ (P.n - 1) := by
      rw [card_twoAdicDomain P.prim (by have := P.rounds_le; omega)]
      exact_mod_cast Nat.pow_le_pow_right two_pos (by omega)
    refine le_trans ?_ hβ
    gcongr

end Params

end CertiFri.Compiled
