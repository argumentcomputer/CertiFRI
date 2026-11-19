import CertiFriProofs.Theory.PcsRbr.Claims
import CertiFriProofs.Theory.Oracle.FiatShamirInterp

/-!
# The whole check as one round-by-round sound protocol

`Theory/Pcs.lean` bounds, one verifier message at a time, the challenges that
leave the doomed state: the `α` round, each folding round, the query round.
This file puts the three bounds into the form the Fiat–Shamir theorems of
`Theory/Oracle/FiatShamir.lean` consume: one public-coin protocol with a
message type, challenge types, a state function `doomed` on its transcripts,
and a proof of `RbrSound`.

## The protocol

Fixed: the domains and degree bounds `S : LdtInstance F` (write `R` for
`S.rounds`), the coset shift `s`, the number `m j` of claims of each level,
the threshold `θ`, and the number `q` of queries. There are `R + 2` rounds.

* Round `0`. The prover sends the claims of every level (`Msg.claims`); each
  claim contains the committed function it is about. The verifier answers with
  `α : F`.
* Round `1 + i`, for `i < R`. The prover sends the codeword of level `i`
  (`Msg.word`). The verifier answers with the folding challenge `β i : F`.
* Round `R + 1`. The prover sends the final word (`Msg.word`). The verifier
  answers with `q` query points of `S.domain 0`.

Messages are functions, not commitments. `Msg` is one type for all rounds, a
record of which round `0` reads one field and the later rounds the other.
`Chal S q i` is `F` for `i ≤ R` and `Fin q → ↥(S.domain 0)` for `i > R`. It is
finite, has decidable equality, and is nonempty when `S.domain 0` is.

`claimsOf`, `alphaOf`, `wordsOf`, `betasOf` and `queriesOf` read a transcript.
`wordsOf t k` and `betasOf t k` are the word and the challenge of round
`1 + k`, as functions of `k : ℕ` that are zero where the transcript holds
nothing.

## The state function

`doomed S s θ q i t`, for a transcript `t` of `i` rounds, with `claims`, `α`,
`c`, `β` read from `t`:

* `i = 0`: doomed.
* The claims do not fail: doomed, whatever `i`. The claims fail
  (`ClaimsFail`) when, at some level, they do not hold away from their opening
  points; see `Theory/PcsRbr/Claims.lean`.
* `i = 1 + k` with `k ≤ R`, and the claims fail: doomed when
  `S.Doomed θ (pcsInput s claims α) c β k`, the doomed state of the low-degree
  test after `k` folding rounds.
* `i = R + 2`, and the claims fail: doomed when
  `S.Doomed θ (pcsInput s claims α) c β R` and the verifier does not accept.
  `Accepts S s t` says that the final word `c R` is a codeword of the last
  level and that every query accepts.

## Results

* `rbrSound`: `RbrSound (R + 2) (doomed S s θ q) (roundError R εα εβ θ q)`. The
  errors are

  * round `0`: `∑ j ∈ range (R + 1), εα j`;
  * round `1 + i`, for `i < R`: `εβ i`;
  * round `R + 1`: `θ ^ q`.

  `fractionLE_alpha`, `fractionLE_fold` and `fractionLE_query` are the three
  kinds of rounds. The `α` round uses the error of one failing level only, so
  the sum is an upper bound for what the proof needs.
* `not_doomed_of_accepts`: a full transcript whose claims fail and on which the
  verifier accepts is not doomed. This is the hypothesis `hE` of
  `prob_fsExperiment_bind_interp_le` for the event "the verifier accepts
  although the claims fail". `not_doomed_of_accepts_of_pcsDoomed` is the same
  with `PcsDoomed`, for claims with no opening point in the coset of its level.
* `doomed_zero`: the empty transcript is doomed. `roundError_nonneg`: the errors
  are nonnegative.
* `claimsOf_mapIdx`, `wordsOf_mapIdx`, `alphaOf_mapIdx`, `betasOf_mapIdx`,
  `queriesOf_mapIdx`: what the accessors return on a transcript whose messages
  are read through an interpretation (`Transcript.mapIdx`).

## Assumptions

* `CurveMCA` on the coset of each level, with error `εα j`, and `StepMCA` for
  each folding round, with error `εβ i`. These are the hypotheses of the three
  escape bounds.
* `s ≠ 0` and `0 ≤ θ`. A transcript whose claims do not fail stays doomed for
  every challenge, and `RbrSound` then asks for `0 ≤ θ ^ q`.
* There is no hypothesis on the opening points. The claims are a message of
  the prover, and the verifier does not check that the opening points avoid
  the cosets; `Theory/PcsRbr/Claims.lean` explains what replaces the
  hypothesis.

## Not modeled, not covered

* Merkle commitments. The claimed functions and the words are functions. In
  the compiled protocol the prover sends Merkle roots;
  `Theory/Oracle/FiatShamirInterp.lean` is the Fiat–Shamir theorem for messages
  that are read, against the log of hash queries, as messages of this protocol.
* The random oracle. `RbrSound` bounds fractions of the challenge types; no
  probability appears here.
* The final polynomial. The final word is a function, and the state function
  asks that it is a codeword. In the compiled protocol it is a polynomial sent
  in the clear.
* The map from query indices to points. A query is a point `x` of
  `S.domain 0`, and the input of level `j` is read at `s * x ^ 2 ^ j`.
* The degree slack in `ClaimsHold` and `ClaimsHoldOff`: the polynomials have
  degree at most `S.degree j`, one more than an honest polynomial has.
* Grinding, which is in `Theory/PcsRbr/Grinding.lean`.
* What `Theory/Pcs.lean` lists as not modeled: the check that the reduced
  opening at height `log_blowup` is zero, and inputs at heights the fold never
  reaches.
-/

namespace CertiFri.PcsRbr

open Polynomial Oracle

universe u v w w'

variable {F : Type u} [Field F]

/-! ## Messages and challenges -/

/-- The prover's message of one round. Round 0 reads the field `claims`: the
evaluation claims of every level, each with the committed function it is
about. A later round `1 + i` reads the field `word`: the codeword committed at
level `i`, or the final word for `i = S.rounds`. The other field of a message
is ignored. -/
structure Msg (F : Type u) (m : ℕ → ℕ) where
  /-- The claims of every level; `m j` is the number of claims of level `j`. -/
  claims : ∀ j, Fin (m j) → Claim F
  /-- The word of a folding round, or the final word. -/
  word : F → F

/-- The challenge type of round `i`: a field element for the `α` round and the
folding rounds (`i ≤ S.rounds`), and `q` query points of the first domain from
round `S.rounds + 1` on. -/
def Chal (S : LdtInstance F) (q : ℕ) (i : ℕ) : Type u :=
  if i ≤ S.rounds then F else (Fin q → ↥(S.domain 0))

section Chal

variable {S : LdtInstance F} {q i : ℕ}

/-- The challenge of a round `i ≤ S.rounds` is a field element. -/
def chalField (h : i ≤ S.rounds) : Chal S q i ≃ F :=
  Equiv.cast (ite_eq_left h)

/-- The challenge of a round `i > S.rounds` is a tuple of query points. -/
def chalQuery (h : ¬ i ≤ S.rounds) : Chal S q i ≃ (Fin q → ↥(S.domain 0)) :=
  Equiv.cast (ite_eq_right h)

/-- The challenge types are finite. -/
instance [Fintype F] : Fintype (Chal S q i) :=
  if h : i ≤ S.rounds then Fintype.ofEquiv F (chalField h).symm
  else Fintype.ofEquiv _ (chalQuery h).symm

/-- Equality of challenges is decidable. -/
instance [DecidableEq F] : DecidableEq (Chal S q i) :=
  if h : i ≤ S.rounds then (chalField h).decidableEq else (chalQuery h).decidableEq

/-- The challenge types are nonempty when the first domain is. -/
instance [Nonempty ↥(S.domain 0)] : Nonempty (Chal S q i) :=
  if h : i ≤ S.rounds then (chalField h).nonempty else (chalQuery h).nonempty

/-- The challenge types are nonempty when the first domain is. -/
theorem Chal.nonempty (h : (S.domain 0).Nonempty) (q i : ℕ) : Nonempty (Chal S q i) :=
  haveI := h.to_subtype
  inferInstance

/-- The field element of a challenge; zero in a query round. -/
def Chal.field (ch : Chal S q i) : F :=
  if h : i ≤ S.rounds then chalField h ch else 0

/-- The query points of a challenge, as field elements; zero in a round whose
challenge is a field element. -/
def Chal.points (ch : Chal S q i) (j : Fin q) : F :=
  if h : i ≤ S.rounds then 0 else (chalQuery h ch j : F)

/-- In a round `i ≤ S.rounds`, the field element of a challenge is the
challenge. -/
theorem Chal.field_of_le (h : i ≤ S.rounds) (ch : Chal S q i) : ch.field = chalField h ch :=
  dite_eq_left h

/-- In a query round, the field element of a challenge is zero. -/
theorem Chal.field_of_not_le (h : ¬ i ≤ S.rounds) (ch : Chal S q i) : ch.field = 0 :=
  dite_eq_right h

/-- In a query round, the points of a challenge are the challenge. -/
theorem Chal.points_of_not_le (h : ¬ i ≤ S.rounds) (ch : Chal S q i) (j : Fin q) :
    ch.points j = chalQuery h ch j :=
  dite_eq_right h

end Chal

/-- A fraction bound moves along a bijection of the challenge type. -/
theorem fractionLE_of_equiv {β : Type*} {γ : Type*} [Fintype β] [Fintype γ] (e : β ≃ γ)
    {p : γ → Prop} {P : β → Prop} {ε : ℝ} (h : FractionLE p ε) (hP : ∀ b, P b → p (e b)) :
    FractionLE P ε := by
  obtain ⟨B, hB, hp⟩ := h
  refine ⟨B.map e.symm.toEmbedding, ?_, fun b hb => ?_⟩
  · rwa [Finset.card_map, Fintype.card_congr e]
  · exact Finset.mem_map.mpr ⟨e b, hp _ (hP b hb), e.symm_apply_apply b⟩

/-! ## Reading a transcript

The accessors return total functions, with a default where the transcript
holds nothing. Those of the messages work for any challenge types and those of
the challenges for any message type, so that they also read a transcript of
commitments, or one with proof-of-work samples. -/

section Accessors

variable {m : ℕ → ℕ} {Chal' : ℕ → Type v} {Msg' : Type w} {S : LdtInstance F} {q : ℕ}

/-- The claims of a transcript: those of the message of round 0. -/
def claimsOf : {i : ℕ} → Transcript (Msg F m) Chal' i → ∀ j, Fin (m j) → Claim F
  | _, .nil => fun _ _ => ⟨0, 0, 0⟩
  | _, .snoc (i := 0) _ msg _ => msg.claims
  | _, .snoc (i := _ + 1) t _ _ => claimsOf t

/-- The words of a transcript: `wordsOf t k` is the word of the message of
round `1 + k`, and zero if the transcript has no such round. -/
def wordsOf : {i : ℕ} → Transcript (Msg F m) Chal' i → ℕ → F → F
  | _, .nil => 0
  | _, .snoc (i := 0) _ _ _ => 0
  | _, .snoc (i := k + 1) t msg _ => Function.update (wordsOf t) k msg.word

/-- The challenge `α` of a transcript: the challenge of round 0. -/
def alphaOf : {i : ℕ} → Transcript Msg' (Chal S q) i → F
  | _, .nil => 0
  | _, .snoc (i := 0) _ _ ch => ch.field
  | _, .snoc (i := _ + 1) t _ _ => alphaOf t

/-- The folding challenges of a transcript: `betasOf t k` is the challenge of
round `1 + k`, and zero if the transcript has no such round or the round is a
query round. -/
def betasOf : {i : ℕ} → Transcript Msg' (Chal S q) i → ℕ → F
  | _, .nil => 0
  | _, .snoc (i := 0) _ _ _ => 0
  | _, .snoc (i := k + 1) t _ ch => Function.update (betasOf t) k ch.field

/-- The query points of a transcript: those of its last challenge. -/
def queriesOf : {i : ℕ} → Transcript Msg' (Chal S q) i → Fin q → F
  | _, .nil => 0
  | _, .snoc _ _ ch => ch.points

/-- The claims of a transcript of one round are those of its message. -/
@[simp] theorem claimsOf_snoc_zero (t : Transcript (Msg F m) Chal' 0) (msg : Msg F m)
    (ch : Chal' 0) : claimsOf (t.snoc msg ch) = msg.claims := rfl

/-- A later round does not change the claims. -/
@[simp] theorem claimsOf_snoc_succ {k : ℕ} (t : Transcript (Msg F m) Chal' (k + 1))
    (msg : Msg F m) (ch : Chal' (k + 1)) : claimsOf (t.snoc msg ch) = claimsOf t := rfl

/-- Round `1 + k` sets word `k`. -/
@[simp] theorem wordsOf_snoc_succ {k : ℕ} (t : Transcript (Msg F m) Chal' (k + 1))
    (msg : Msg F m) (ch : Chal' (k + 1)) :
    wordsOf (t.snoc msg ch) = Function.update (wordsOf t) k msg.word := rfl

/-- The `α` of a transcript of one round is its challenge. -/
@[simp] theorem alphaOf_snoc_zero (t : Transcript Msg' (Chal S q) 0) (msg : Msg')
    (ch : Chal S q 0) : alphaOf (t.snoc msg ch) = ch.field := rfl

/-- A later round does not change `α`. -/
@[simp] theorem alphaOf_snoc_succ {k : ℕ} (t : Transcript Msg' (Chal S q) (k + 1)) (msg : Msg')
    (ch : Chal S q (k + 1)) : alphaOf (t.snoc msg ch) = alphaOf t := rfl

/-- Round `1 + k` sets folding challenge `k`. -/
@[simp] theorem betasOf_snoc_succ {k : ℕ} (t : Transcript Msg' (Chal S q) (k + 1)) (msg : Msg')
    (ch : Chal S q (k + 1)) :
    betasOf (t.snoc msg ch) = Function.update (betasOf t) k ch.field := rfl

/-- The query points of a nonempty transcript are those of its last challenge. -/
@[simp] theorem queriesOf_snoc {i : ℕ} (t : Transcript Msg' (Chal S q) i) (msg : Msg')
    (ch : Chal S q i) : queriesOf (t.snoc msg ch) = ch.points := rfl

/-- Reading the messages differently does not change `α`. -/
@[simp] theorem alphaOf_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (Chal S q) i), alphaOf (t.mapIdx f) = alphaOf t
  | _, .nil => rfl
  | _, .snoc (i := 0) _ _ _ => rfl
  | _, .snoc (i := _ + 1) t _ _ => alphaOf_mapIdx f t

/-- Reading the messages differently does not change the folding challenges. -/
@[simp] theorem betasOf_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (Chal S q) i), betasOf (t.mapIdx f) = betasOf t
  | _, .nil => rfl
  | _, .snoc (i := 0) _ _ _ => rfl
  | _, .snoc (i := _ + 1) t _ _ => by
    rw [Transcript.mapIdx_snoc, betasOf_snoc_succ, betasOf_snoc_succ, betasOf_mapIdx f t]

/-- Reading the messages differently does not change the query points. -/
@[simp] theorem queriesOf_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (Chal S q) i), queriesOf (t.mapIdx f) = queriesOf t
  | _, .nil => rfl
  | _, .snoc _ _ _ => rfl

/-- The claims of a transcript whose messages are read through `f`: those of
the reading of its message of round 0. -/
theorem claimsOf_mapIdx (f : ℕ → Msg' → Msg F m) :
    ∀ {i : ℕ} (t : Transcript Msg' Chal' i) {m₀ : Msg'}, t.msgs[0]? = some m₀ →
      claimsOf (t.mapIdx f) = (f 0 m₀).claims
  | _, .nil, _, h => by simp at h
  | _, .snoc (i := 0) t msg ch, m₀, h => by
    have hlast := List.getElem?_concat_length (l := t.msgs) (a := msg)
    rw [t.length_msgs] at hlast
    rw [Transcript.msgs_snoc, hlast] at h
    rw [Transcript.mapIdx_snoc, claimsOf_snoc_zero, Option.some.inj h]
  | _, .snoc (i := k + 1) t msg ch, m₀, h => by
    rw [Transcript.msgs_snoc,
      List.getElem?_append_left (by rw [t.length_msgs]; exact Nat.succ_pos k)] at h
    rw [Transcript.mapIdx_snoc, claimsOf_snoc_succ, claimsOf_mapIdx f t h]

/-- Word `k` of a transcript whose messages are read through `f`: that of the
reading of its message of round `1 + k`. -/
theorem wordsOf_mapIdx (f : ℕ → Msg' → Msg F m) :
    ∀ {i : ℕ} (t : Transcript Msg' Chal' i) {k : ℕ} {mk : Msg'}, t.msgs[k + 1]? = some mk →
      wordsOf (t.mapIdx f) k = (f (k + 1) mk).word
  | _, .nil, _, _, h => by simp at h
  | _, .snoc (i := 0) t msg ch, k, mk, h => by
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    rw [Transcript.msgs_snoc, List.length_append, t.length_msgs, List.length_singleton] at hlt
    omega
  | _, .snoc (i := j + 1) t msg ch, k, mk, h => by
    rw [Transcript.mapIdx_snoc, wordsOf_snoc_succ]
    rcases eq_or_ne k j with rfl | hkj
    · have hlast := List.getElem?_concat_length (l := t.msgs) (a := msg)
      rw [t.length_msgs] at hlast
      rw [Transcript.msgs_snoc, hlast] at h
      rw [Function.update_self, Option.some.inj h]
    · have hlt := (List.getElem?_eq_some_iff.mp h).1
      rw [Transcript.msgs_snoc, List.length_append, t.length_msgs, List.length_singleton] at hlt
      rw [Transcript.msgs_snoc,
        List.getElem?_append_left (by rw [t.length_msgs]; omega)] at h
      rw [Function.update_of_ne hkj, wordsOf_mapIdx f t h]

end Accessors

/-! ## The state function -/

section State

variable [DecidableEq F] {m : ℕ → ℕ}

/-- What the verifier checks at the end, on a transcript with a query round:
the final word is a codeword of the last level, and every query accepts. The
inputs of the low-degree test are the reduced openings of the claims with the
challenge `α` of the transcript. -/
def Accepts (S : LdtInstance F) (s : F) {q i : ℕ} (t : Transcript (Msg F m) (Chal S q) i) :
    Prop :=
  IsCodeword (S.domain S.rounds) (S.degree S.rounds) (wordsOf t S.rounds) ∧
    ∀ j, QueryAccepts S.rounds (pcsInput s (claimsOf t) (alphaOf t)) (wordsOf t) (betasOf t)
      (queriesOf t j)

/-- The state function of the whole check.

* The empty transcript is doomed.
* A transcript whose claims do not fail is doomed.
* A transcript of `1 + k` rounds with `k ≤ S.rounds`, whose claims fail, is
  doomed when the low-degree test is in its doomed state after `k` folding
  rounds: some reduced opening is not `θ`-close to its code, and the first `k`
  folding challenges were good.
* A longer transcript, whose claims fail, is doomed when the low-degree test
  is in its doomed state after all folding rounds and the verifier does not
  accept. -/
def doomed (S : LdtInstance F) (s : F) (θ : ℝ) (q : ℕ) :
    ∀ i, Transcript (Msg F m) (Chal S q) i → Prop
  | 0, _ => True
  | i + 1, t =>
    ClaimsFail S s θ (claimsOf t) →
      if i ≤ S.rounds then
        S.Doomed θ (pcsInput s (claimsOf t) (alphaOf t)) (wordsOf t) (betasOf t) i
      else
        S.Doomed θ (pcsInput s (claimsOf t) (alphaOf t)) (wordsOf t) (betasOf t) S.rounds ∧
          ¬ Accepts S s t

/-- The empty transcript is doomed. -/
theorem doomed_zero (S : LdtInstance F) (s : F) (θ : ℝ) (q : ℕ)
    (t : Transcript (Msg F m) (Chal S q) 0) : doomed S s θ q 0 t :=
  trivial

variable {S : LdtInstance F} {s : F} {θ : ℝ} {q : ℕ}

/-- A transcript whose claims do not fail is doomed. -/
theorem doomed_of_not_claimsFail {i : ℕ} {t : Transcript (Msg F m) (Chal S q) i}
    (h : ¬ ClaimsFail S s θ (claimsOf t)) : doomed S s θ q i t := by
  cases i with
  | zero => trivial
  | succ i => exact fun hf => absurd hf h

/-- After `α` and `k ≤ S.rounds` folding rounds: the transcript is doomed when
its claims do not fail or the low-degree test is in its doomed state after `k`
rounds. -/
theorem doomed_succ_iff {k : ℕ} (hk : k ≤ S.rounds) (t : Transcript (Msg F m) (Chal S q) (k + 1)) :
    doomed S s θ q (k + 1) t ↔ (ClaimsFail S s θ (claimsOf t) →
      S.Doomed θ (pcsInput s (claimsOf t) (alphaOf t)) (wordsOf t) (betasOf t) k) := by
  simp only [doomed, ite_eq_left hk]

/-- After the query round: the transcript is doomed when its claims do not
fail, or the low-degree test is in its doomed state after all folding rounds
and the verifier does not accept. -/
theorem doomed_succ_iff_of_lt {k : ℕ} (hk : S.rounds < k)
    (t : Transcript (Msg F m) (Chal S q) (k + 1)) :
    doomed S s θ q (k + 1) t ↔ (ClaimsFail S s θ (claimsOf t) →
      S.Doomed θ (pcsInput s (claimsOf t) (alphaOf t)) (wordsOf t) (betasOf t) S.rounds ∧
        ¬ Accepts S s t) := by
  simp only [doomed, ite_eq_right (Nat.not_le.mpr hk)]

/-- The final event. A full transcript whose claims fail and on which the
verifier accepts is not doomed. -/
theorem not_doomed_of_accepts (t : Transcript (Msg F m) (Chal S q) (S.rounds + 2))
    (hfail : ClaimsFail S s θ (claimsOf t)) (hacc : Accepts S s t) :
    ¬ doomed S s θ q (S.rounds + 2) t := fun hd =>
  ((doomed_succ_iff_of_lt (Nat.lt_succ_self _) t).mp hd hfail).2 hacc

/-- The final event for claims with no opening point in the coset of its
level. A full transcript whose claims do not hold at some level
(`PcsDoomed`) and on which the verifier accepts is not doomed. -/
theorem not_doomed_of_accepts_of_pcsDoomed (t : Transcript (Msg F m) (Chal S q) (S.rounds + 2))
    (hz : ∀ j ≤ S.rounds, ∀ k, (claimsOf t j k).z ∉ (S.domain j).image (s * ·))
    (hfail : PcsDoomed S s θ (claimsOf t)) (hacc : Accepts S s t) :
    ¬ doomed S s θ q (S.rounds + 2) t :=
  not_doomed_of_accepts t ((claimsFail_iff_pcsDoomed hz).mpr hfail) hacc

end State

/-! ## Round-by-round soundness -/

/-- The error of each round: `∑ j ∈ range (R + 1), εα j` for the `α` round,
`εβ i` for the folding round `1 + i` with `i < R`, and `θ ^ q` for the query
round `R + 1` (and beyond, where no round is). -/
def roundError (R : ℕ) (εα εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) : ℕ → ℝ
  | 0 => ∑ j ∈ Finset.range (R + 1), εα j
  | i + 1 => if i < R then εβ i else θ ^ q

/-- The error of the `α` round. -/
@[simp] theorem roundError_zero (R : ℕ) (εα εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) :
    roundError R εα εβ θ q 0 = ∑ j ∈ Finset.range (R + 1), εα j := rfl

/-- The error of a folding round. -/
theorem roundError_succ_of_lt {R i : ℕ} (h : i < R) (εα εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) :
    roundError R εα εβ θ q (i + 1) = εβ i :=
  ite_eq_left h

/-- The error from the query round on. -/
theorem roundError_succ_of_not_lt {R i : ℕ} (h : ¬ i < R) (εα εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) :
    roundError R εα εβ θ q (i + 1) = θ ^ q :=
  ite_eq_right h

/-- The error of the query round. -/
@[simp] theorem roundError_last (R : ℕ) (εα εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) :
    roundError R εα εβ θ q (R + 1) = θ ^ q :=
  roundError_succ_of_not_lt (Nat.lt_irrefl R) εα εβ θ q

section Rounds

variable [Fintype F] [DecidableEq F] {S : LdtInstance F} {s : F} {θ : ℝ} {q : ℕ} {m : ℕ → ℕ}

/-- The `α` round. Whatever claims the prover sends, at most a
`∑ j ∈ range (rounds + 1), εα j` fraction of the values of `α` give a
transcript that is not doomed. -/
theorem fractionLE_alpha (hs : s ≠ 0) {εα : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (t : Transcript (Msg F m) (Chal S q) 0) (msg : Msg F m) :
    FractionLE (fun ch : Chal S q 0 => ¬ doomed S s θ q 1 (t.snoc msg ch))
      (∑ j ∈ Finset.range (S.rounds + 1), εα j) := by
  have h0 : (0 : ℕ) ≤ S.rounds := Nat.zero_le _
  by_cases hf : ClaimsFail S s θ msg.claims
  · refine fractionLE_of_equiv (chalField h0) (hf.fractionLE_close hs hmca) fun ch hch i hi => ?_
    by_contra hfar
    refine hch ((doomed_succ_iff h0 _).mpr fun _ => (S.doomed_zero_iff θ _ _ _).mpr ⟨i, hi, ?_⟩)
    rwa [claimsOf_snoc_zero, alphaOf_snoc_zero, Chal.field_of_le h0]
  · have hnonneg : 0 ≤ ∑ j ∈ Finset.range (S.rounds + 1), εα j := Finset.sum_nonneg fun j hj =>
      nonneg_of_curveMCA (hmca j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    exact (FractionLE.false.mono_right hnonneg).mono_left fun ch hch =>
      hch (doomed_of_not_claimsFail hf)

/-- Folding round `k`. From a doomed transcript and whatever word the prover
sends, at most a fraction `ε` of the values of the folding challenge give a
transcript that is not doomed. -/
theorem fractionLE_fold {k : ℕ} (hk : k < S.rounds) {ε : ℝ}
    (hstep : StepMCA (S.domain k) (S.domain (k + 1)) (S.degree (k + 1)) θ ε)
    (t : Transcript (Msg F m) (Chal S q) (k + 1)) (msg : Msg F m)
    (hd : doomed S s θ q (k + 1) t) :
    FractionLE (fun ch : Chal S q (k + 1) => ¬ doomed S s θ q (k + 2) (t.snoc msg ch)) ε := by
  classical
  have hk1 : k + 1 ≤ S.rounds := hk
  by_cases hf : ClaimsFail S s θ (claimsOf t)
  · have hdk := ((doomed_succ_iff hk.le t).mp hd hf).congr
      (c' := Function.update (wordsOf t) k msg.word) (β' := betasOf t)
      (fun j hj => Function.update_of_ne hj.ne _ _) (fun _ _ => rfl)
    refine fractionLE_of_equiv (chalField hk1)
      (fractionLE_iff_card_filter.mpr (hdk.card_escape_le (hstep _))) fun ch hch hgood => hch ?_
    rw [doomed_succ_iff hk1]
    intro _
    rwa [claimsOf_snoc_succ, alphaOf_snoc_succ, wordsOf_snoc_succ, betasOf_snoc_succ,
      Chal.field_of_le hk1]
  · exact (FractionLE.false.mono_right (Compose.nonneg_of_stepMCA hstep)).mono_left fun ch hch =>
      hch (doomed_of_not_claimsFail hf)

/-- The query round. From a doomed transcript and whatever final word the
prover sends, at most a fraction `θ ^ q` of the `q`-tuples of query points give
a transcript that is not doomed. -/
theorem fractionLE_query (hθ : 0 ≤ θ) (t : Transcript (Msg F m) (Chal S q) (S.rounds + 1))
    (msg : Msg F m) (hd : doomed S s θ q (S.rounds + 1) t) :
    FractionLE (fun ch : Chal S q (S.rounds + 1) =>
      ¬ doomed S s θ q (S.rounds + 2) (t.snoc msg ch)) (θ ^ q) := by
  classical
  have hR : ¬ S.rounds + 1 ≤ S.rounds := Nat.not_succ_le_self _
  have hθq : 0 ≤ θ ^ q := pow_nonneg hθ q
  -- The state after the round, as far as it does not depend on the challenge.
  have hsnoc : ∀ ch : Chal S q (S.rounds + 1),
      doomed S s θ q (S.rounds + 2) (t.snoc msg ch) ↔ (ClaimsFail S s θ (claimsOf t) →
        S.Doomed θ (pcsInput s (claimsOf t) (alphaOf t))
            (Function.update (wordsOf t) S.rounds msg.word)
            (Function.update (betasOf t) S.rounds 0) S.rounds ∧
          ¬ (IsCodeword (S.domain S.rounds) (S.degree S.rounds) msg.word ∧
            ∀ j, QueryAccepts S.rounds (pcsInput s (claimsOf t) (alphaOf t))
              (Function.update (wordsOf t) S.rounds msg.word)
              (Function.update (betasOf t) S.rounds 0) (chalQuery hR ch j))) := fun ch => by
    rw [doomed_succ_iff_of_lt (Nat.lt_succ_self _)]
    simp only [Accepts, claimsOf_snoc_succ, alphaOf_snoc_succ, wordsOf_snoc_succ,
      betasOf_snoc_succ, queriesOf_snoc, Chal.field_of_not_le hR, Chal.points_of_not_le hR,
      Function.update_self]
  by_cases hf : ClaimsFail S s θ (claimsOf t)
  · have hdR := ((doomed_succ_iff le_rfl t).mp hd hf).congr
      (c' := Function.update (wordsOf t) S.rounds msg.word)
      (β' := Function.update (betasOf t) S.rounds 0)
      (fun j hj => Function.update_of_ne hj.ne _ _) (fun j hj => Function.update_of_ne hj.ne _ _)
    by_cases hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) msg.word
    · have hcount := hdR.card_accepting_queries_le (by rwa [Function.update_self]) q
      refine fractionLE_of_equiv (chalQuery hR) (fractionLE_iff_card_filter.mpr
        (hcount.trans_eq ?_)) fun ch hch => ?_
      · rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, Nat.cast_pow, mul_pow]
      · by_contra hrej
        exact hch ((hsnoc ch).mpr fun _ => ⟨hdR, fun hacc => hrej hacc.2⟩)
    · exact (FractionLE.false.mono_right hθq).mono_left fun ch hch =>
        hch ((hsnoc ch).mpr fun _ => ⟨hdR, fun hacc => hfinal hacc.1⟩)
  · exact (FractionLE.false.mono_right hθq).mono_left fun ch hch =>
      hch (doomed_of_not_claimsFail hf)

/-- **Round-by-round soundness of the whole check.** The protocol has
`S.rounds + 2` rounds: the claims and `α`, one round per folding step, and the
final word with the queries. Assume `CurveMCA` on the coset of every level with
error `εα j`, and `StepMCA` for every folding round with error `εβ i`. Then the
state function `doomed` is round-by-round sound with the errors
`∑ j ∈ range (rounds + 1), εα j` for `α`, `εβ i` for folding round `i`, and
`θ ^ q` for the queries. -/
theorem rbrSound (S : LdtInstance F) {s : F} (hs : s ≠ 0) {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ)
    {m : ℕ → ℕ} {εα εβ : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (εβ i)) :
    RbrSound (S.rounds + 2) (doomed S s θ q (m := m)) (roundError S.rounds εα εβ θ q) := by
  intro i hi t msg hd
  rcases i with _ | k
  · exact fractionLE_alpha hs hmca t msg
  · rcases Nat.lt_or_ge k S.rounds with hk | hk
    · rw [roundError_succ_of_lt hk]
      exact fractionLE_fold hk (hstep k hk) t msg hd
    · obtain rfl : k = S.rounds := by omega
      rw [roundError_last]
      exact fractionLE_query hθ t msg hd

/-- Under the hypotheses of `rbrSound`, the error of every round is
nonnegative. -/
theorem roundError_nonneg (S : LdtInstance F) {s : F} {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ) {m : ℕ → ℕ}
    {εα εβ : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j))
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (εβ i)) (i : ℕ) :
    0 ≤ roundError S.rounds εα εβ θ q i := by
  rcases i with _ | k
  · exact Finset.sum_nonneg fun j hj =>
      nonneg_of_curveMCA (hmca j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  · by_cases hk : k < S.rounds
    · rw [roundError_succ_of_lt hk]
      exact Compose.nonneg_of_stepMCA (hstep k hk)
    · rw [roundError_succ_of_not_lt hk]
      exact pow_nonneg hθ q

end Rounds

end CertiFri.PcsRbr
