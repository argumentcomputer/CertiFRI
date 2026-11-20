import CertiFriProofs.Theory.Oracle.FiatShamir

/-!
# Fiat–Shamir chains whose messages depend on earlier challenges

In `Theory/Oracle/FiatShamir.lean` the verifier derives the challenges for a
fixed sequence of prover messages (`derive`, `fsTranscript`). A verifier may
also absorb a value it computed from an earlier challenge: the STARK verifier
absorbs each lookup challenge back before it squeezes the next one. The message
of a round is then a function of the transcript so far.

* `fsTranscriptA f next i`: the transcript of `i` rounds in which the message
  of round `j` is `next j t`, for the transcript `t` of the first `j` rounds,
  and the challenges are the answers of `f` along the chain.
* `fsTranscriptA_eq_fsTranscript`: it is the chain of `fsTranscript` on its
  own messages.
* `deriveA Y' next i`: the computation that derives it with one query per
  round. `queryBound_deriveA`, `run_deriveA`, `supports_of_outcome_deriveA`
  and `OracleComp.Outcome.eq_fsTranscriptA` are the facts
  `FiatShamir.lean` proves of `derive`.

`derive Y' ms` is the case `next := fun j _ => ms j`.
-/

namespace CertiFri.Oracle

universe u v u'

variable {Msg : Type u} {Chal : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}

/-- The transcript of `i` rounds whose message of round `j` is `next j t`, for
the transcript `t` of the first `j` rounds, with the challenges the function
`f` gives along the chain. -/
def fsTranscriptA (f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x)
    (next : ∀ i, Transcript Msg Chal i → Msg) : (i : ℕ) → Transcript Msg Chal i
  | 0 => .nil
  | i + 1 => (fsTranscriptA f next i).snoc (next i (fsTranscriptA f next i))
      (f (.chal (fsTranscriptA f next i) (next i (fsTranscriptA f next i))))

/-- The chain with computed messages is the chain on the messages it
computes. -/
theorem fsTranscriptA_eq_fsTranscript (f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x)
    (next : ∀ i, Transcript Msg Chal i → Msg) (i : ℕ) :
    fsTranscriptA f next i = fsTranscript f (fun j => next j (fsTranscriptA f next j)) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [fsTranscript, ← ih]
    rfl

open OracleComp

/-- Derive the challenges of `i` rounds, with one query per round along the
chain; the message of each round is computed from the transcript so far. -/
def deriveA (Y' : X' → Type v) (next : ∀ i, Transcript Msg Chal i → Msg) :
    (i : ℕ) → OracleComp (FSAnswer (Msg := Msg) Chal Y') (Transcript Msg Chal i)
  | 0 => .pure .nil
  | i + 1 => (deriveA Y' next i).bind fun t =>
      .queryBind (.chal t (next i t)) fun c => .pure (t.snoc (next i t) c)

/-- Deriving the challenges of `i` rounds takes at most `i` queries. -/
theorem queryBound_deriveA (next : ∀ i, Transcript Msg Chal i → Msg) :
    ∀ i : ℕ, (deriveA (Chal := Chal) Y' next i).QueryBound i
  | 0 => trivial
  | i + 1 => (queryBound_deriveA next i).bind fun _ _ => trivial

/-- Against a fixed function, `deriveA` computes `fsTranscriptA`. -/
theorem run_deriveA (f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x)
    (next : ∀ i, Transcript Msg Chal i → Msg) :
    ∀ i : ℕ, (deriveA Y' next i).run f = fsTranscriptA f next i
  | 0 => rfl
  | i + 1 => by
    rw [deriveA, run_bind, run_deriveA f next i]
    rfl

variable [DecidableEq (FSQuery Msg Chal X')]

/-- After `deriveA`, the log answers the chain of the derived transcript. -/
theorem supports_of_outcome_deriveA {next : ∀ i, Transcript Msg Chal i → Msg} :
    ∀ {i : ℕ} {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} {t : Transcript Msg Chal i},
      Outcome (deriveA Y' next i) l t l' → Supports l' t
  | 0, _, _, _, h => by
    obtain ⟨rfl, _⟩ := h
    trivial
  | i + 1, l, l', t, h => by
    rw [deriveA, outcome_bind] at h
    obtain ⟨t₀, l₁, h₀, h⟩ := h
    obtain ⟨c, l₂, hc, rfl, rfl⟩ := outcome_queryBind.mp h
    exact ⟨(supports_of_outcome_deriveA h₀).of_prefix hc.prefix, hc.dlookup_query⟩

/-- The transcript `deriveA` returns is the one any function that agrees with
the final log gives. -/
theorem OracleComp.Outcome.eq_fsTranscriptA {next : ∀ i, Transcript Msg Chal i → Msg} {i : ℕ}
    {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} {t : Transcript Msg Chal i}
    (h : Outcome (deriveA Y' next i) l t l') {f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x}
    (hf : ∀ x y, l'.dlookup x = some y → f x = y) : t = fsTranscriptA f next i := by
  rw [← run_deriveA, h.run_eq hf]

end CertiFri.Oracle
