import Mathlib
import CertiFriProofs.Theory.Oracle.Balanced
import CertiFriProofs.Theory.PcsRbr.Grinding
import CertiFriProofs.Theory.Compiled.Verifier

/-!
# One challenge type for every round

The opening protocol (`Theory/PcsRbr.lean`) has challenge types that depend on
its parameters: a field element in the batching round and the folding rounds, a
tuple of points of the first domain in the query round, each with some
proof-of-work bits. The parameters depend on the heights of the committed
matrices, which a prover of the STARK chooses. So that one random oracle serves
every choice, the STARK is analysed with the same answer type in every round.

* `UAns K slots width` is that type: a field element and `slots` numbers below
  `2 ^ width`. `UAns.field` is the field element. `UAns.bits u k b` is the
  `k`-th number reduced to `b` bits: what the `k`-th squeeze of bits of a round
  returns when it asks for `b` bits.
* `pcsChal P bits j u` reads the challenge of round `j` of the opening protocol
  with parameters `P` off a uniform answer: the proof-of-work bits are the first
  number, the field challenge is the field element, and query point `t` is the
  point whose index is the next number (the first number is skipped when the
  round has a proof-of-work check).
* `fractionLE_pcsChal`: a fraction bound on the challenges of round `j` holds
  for the uniform answers read through `pcsChal`, when there are more slots
  than queries and the width is at least the number of bits asked for.

## Modelling

The components of an answer are independent and uniform. In Plonky3 the
proof-of-work bits, a field challenge and the query indices of a round are
successive outputs of one sponge, and a sample of `b` bits is the low bits of a
field element.
-/

namespace CertiFri.Stark

open CertiFri.Oracle CertiFri.PcsRbr

/-- A uniform answer to a challenge query: a field element and `slots` numbers
below `2 ^ width`. -/
abbrev UAns (K : Type) (slots width : ℕ) : Type :=
  K × (Fin slots → Fin (2 ^ width))

namespace UAns

variable {K : Type} {slots width : ℕ}

/-- The field challenge of an answer. -/
def field (u : UAns K slots width) : K := u.1

/-- The `k`-th number of an answer, reduced to `b` bits; zero if the answer has
no such number. -/
def bits (u : UAns K slots width) (k b : ℕ) : ℕ :=
  if h : k < slots then (u.2 ⟨k, h⟩ : ℕ) % 2 ^ b else 0

/-- A number reduced to `b` bits is below `2 ^ b`. -/
theorem bits_lt (u : UAns K slots width) (k b : ℕ) : u.bits k b < 2 ^ b := by
  unfold bits
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos b)
  · exact Nat.two_pow_pos b

/-- The `k`-th number of an answer that has one, reduced to `b` bits. -/
theorem bits_of_lt (u : UAns K slots width) {k : ℕ} (h : k < slots) (b : ℕ) :
    u.bits k b = (u.2 ⟨k, h⟩ : ℕ) % 2 ^ b :=
  dite_eq_left h

end UAns

section Pcs

variable {K : Type} [Field K] [DecidableEq K] {slots width : ℕ}

/-- The challenge of round `j` of the opening protocol with parameters `P` and
proof-of-work bits `bits`, read off a uniform answer. -/
noncomputable def pcsChal (P : Compiled.Params K) (bits : ℕ → ℕ) (j : ℕ)
    (u : UAns K slots width) : GrindChal bits (Chal P.ldt P.queries) j :=
  (⟨u.bits 0 (bits j), u.bits_lt 0 (bits j)⟩,
    if h : j ≤ P.ldt.rounds then (chalField h).symm u.field
    else (chalQuery h).symm fun t =>
      ⟨pointOfIndex P.ω P.n P.n (u.bits (t.val + if bits j = 0 then 0 else 1) P.n), by
        simpa using pointOfIndex_mem_twoAdicDomain P.prim P.n
          (u.bits (t.val + if bits j = 0 then 0 else 1) P.n)⟩)

variable (P : Compiled.Params K) (bits : ℕ → ℕ) (j : ℕ) (u : UAns K slots width)

/-- The proof-of-work bits of a round are the first number of the answer. -/
theorem pcsChal_pow : ((pcsChal P bits j u).1 : ℕ) = u.bits 0 (bits j) := rfl

/-- In a round with a field challenge, it is the field element of the answer. -/
theorem field_pcsChal (h : j ≤ P.rounds) : (pcsChal P bits j u).2.field = u.field := by
  have h' : j ≤ P.ldt.rounds := h
  rw [Chal.field_of_le h']
  simp only [pcsChal, dite_eq_left h', Equiv.apply_symm_apply]

/-- In a later round the field challenge reads zero. -/
theorem field_pcsChal_of_not_le (h : ¬ j ≤ P.rounds) : (pcsChal P bits j u).2.field = 0 :=
  Chal.field_of_not_le (S := P.ldt) h _

/-- In the query round, query point `t` is the point of the next number of the
answer, read as an index. -/
theorem points_pcsChal (h : ¬ j ≤ P.rounds) (t : Fin P.queries) :
    (pcsChal P bits j u).2.points t =
      pointOfIndex P.ω P.n P.n (u.bits (t.val + if bits j = 0 then 0 else 1) P.n) := by
  have h' : ¬ j ≤ P.ldt.rounds := h
  rw [Chal.points_of_not_le h']
  simp only [pcsChal, dite_eq_right h', Equiv.apply_symm_apply]

/-- In the query round, the index of query point `t` is the next number of the
answer. -/
theorem indexOf_points_pcsChal (h : ¬ j ≤ P.rounds) (t : Fin P.queries) :
    P.indexOf ((pcsChal P bits j u).2.points t) =
      u.bits (t.val + if bits j = 0 then 0 else 1) P.n := by
  rw [points_pcsChal P bits j u h t]
  exact P.indexOf_pointOfIndex (u.bits_lt _ _)

/-- The point of the first domain named by an index below `2 ^ n`. -/
private def pointOf (i : Fin (2 ^ P.n)) : ↥(P.ldt.domain 0) :=
  ⟨pointOfIndex P.ω P.n P.n i, by simpa using pointOfIndex_mem_twoAdicDomain P.prim P.n i⟩

/-- The indices below `2 ^ n` are in bijection with the points of the first
domain. -/
private theorem pointOf_bijective : Function.Bijective (pointOf P) := by
  constructor
  · intro a b hab
    exact Fin.ext ((pointOfIndex_inj P.prim le_rfl a.2 b.2).mp (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := exists_pointOfIndex_eq P.prim le_rfl (x := x) (by simpa using hx)
    exact ⟨⟨i, hi⟩, rfl⟩

/-- Reading each of `q` numbers below `2 ^ width` as the index of a point of
the first domain is balanced. -/
private theorem balanced_points (hn : P.n ≤ width) (q : ℕ) :
    Balanced (fun (v : Fin q → Fin (2 ^ width)) (t : Fin q) =>
      pointOf P ⟨(v t : ℕ) % 2 ^ P.n, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) :=
  Balanced.postcomp ((Balanced.of_bijective (pointOf_bijective P)).comp (Balanced.finMod hn))

/-- In a round with a field challenge, reading the challenge off a uniform
answer is balanced: the proof-of-work bits are the first number and the
challenge is the field element. -/
private theorem balanced_pcsChal_of_le [Finite K] (hslots : 0 < slots) (hbits : bits j ≤ width)
    (h : j ≤ P.ldt.rounds) :
    Balanced (pcsChal P bits j :
      UAns K slots width → GrindChal bits (Chal P.ldt P.queries) j) := by
  have h0 : Balanced (fun v : Fin slots → Fin (2 ^ width) => v ⟨0, hslots⟩) := Balanced.eval _
  have h1 := Balanced.prodMap (Balanced.of_equiv (chalField (q := P.queries) h).symm)
    ((Balanced.finMod hbits).comp h0)
  refine ((Balanced.of_equiv (Equiv.prodComm _ _)).comp h1).congr fun u => ?_
  refine Prod.ext (Fin.ext ?_) ?_
  · exact (UAns.bits_of_lt u hslots (bits j)).symm
  · simp only [pcsChal, dite_eq_left h]
    rfl

/-- In the query round, reading the challenge off a uniform answer is
balanced. With a proof-of-work check, its bits are the first number and the
query points are the next ones. Without one, the bits carry nothing and the
query points start at the first number. -/
private theorem balanced_pcsChal_of_not_le [Finite K] (hslots : P.queries + 1 ≤ slots)
    (hbits : bits j ≤ width) (hn : P.n ≤ width) (h : ¬ j ≤ P.ldt.rounds) :
    Balanced (pcsChal P bits j :
      UAns K slots width → GrindChal bits (Chal P.ldt P.queries) j) := by
  have hpts := (Balanced.of_equiv (chalQuery (q := P.queries) h).symm).comp
    (balanced_points P (width := width) hn P.queries)
  by_cases hb : bits j = 0
  · have hsub : Subsingleton (Fin (2 ^ bits j)) :=
      Fin.subsingleton_iff_le_one.mpr (by rw [hb, pow_zero])
    have hres : Balanced (fun (v : Fin slots → Fin (2 ^ width)) (t : Fin P.queries) =>
        v (Fin.castLE (Nat.le_of_succ_le hslots) t)) :=
      Balanced.precomp_injective (Fin.castLE_injective _)
    have hq := hpts.comp (hres.comp (Balanced.snd (β := K)))
    refine (hq.prodMk_const ⟨0, Nat.two_pow_pos _⟩).congr fun u => ?_
    refine Prod.ext (Subsingleton.elim _ _) ?_
    simp only [pcsChal, dite_eq_right h]
    refine congrArg (chalQuery h).symm (funext fun t => Subtype.ext ?_)
    change pointOfIndex P.ω P.n P.n _ = pointOfIndex P.ω P.n P.n _
    rw [ite_eq_left hb, Nat.add_zero,
      UAns.bits_of_lt u (lt_of_lt_of_le t.2 (Nat.le_of_succ_le hslots))]
    rfl
  · have hres : Balanced (fun (v : Fin slots → Fin (2 ^ width)) (t : Fin (P.queries + 1)) =>
        v (Fin.castLE hslots t)) :=
      Balanced.precomp_injective (Fin.castLE_injective _)
    have hsplit := (Balanced.finConsSplit P.queries).comp (hres.comp (Balanced.snd (β := K)))
    refine ((Balanced.prodMap (Balanced.finMod hbits) hpts).comp hsplit).congr fun u => ?_
    refine Prod.ext (Fin.ext ?_) ?_
    · exact (UAns.bits_of_lt u (by omega) (bits j)).symm
    · simp only [pcsChal, dite_eq_right h]
      refine congrArg (chalQuery h).symm (funext fun t => Subtype.ext ?_)
      change pointOfIndex P.ω P.n P.n _ = pointOfIndex P.ω P.n P.n _
      rw [ite_eq_right hb, UAns.bits_of_lt u (by omega)]
      rfl

/-- **A fraction bound on the challenges of a round of the opening protocol
holds for the uniform answers.** There are more slots than queries, and the
width is at least the number of proof-of-work bits of the round and the log of
the size of the first domain. -/
theorem fractionLE_pcsChal [Fintype K] (hslots : P.queries + 1 ≤ slots) (hbits : bits j ≤ width)
    (hn : P.n ≤ width) {p : GrindChal bits (Chal P.ldt P.queries) j → Prop} {ε : ℝ}
    (h : FractionLE p ε) : FractionLE (fun u : UAns K slots width => p (pcsChal P bits j u)) ε := by
  refine FractionLE.comap ?_ h
  by_cases hj : j ≤ P.ldt.rounds
  · exact balanced_pcsChal_of_le P bits j (by omega) hbits hj
  · exact balanced_pcsChal_of_not_le P bits j hslots hbits hn hj

omit [Field K] [DecidableEq K] in
/-- A fraction bound on the field holds for the field challenges of the uniform
answers. -/
theorem fractionLE_field [Fintype K] {p : K → Prop} {ε : ℝ} (h : FractionLE p ε) :
    FractionLE (fun u : UAns K slots width => p u.field) ε :=
  FractionLE.comap Balanced.fst h

end Pcs

end CertiFri.Stark
