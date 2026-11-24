import Mathlib
import CertiFriProofs.Theory.Oracle.BadEvent

/-!
# Balanced maps

A map `f : α → β` between finite types is *balanced* when it is a projection
up to a bijection: `α` is in bijection with `β × γ`, for some finite type `γ`,
in such a way that `f` is the first component. Every fibre of a balanced map
has the same size, so the image under `f` of a uniform element of `α` is a
uniform element of `β`.

This is what allows one challenge type for every round of a protocol: a round
that needs a challenge of type `β` reads it off a uniform answer of a larger
type `α` through a balanced map, and a bound on a fraction of `β` gives the
same bound on the fraction of `α` (`FractionLE.comap`).

## Contents

* `Balanced f`, and its closure properties:
  * `Balanced.congr`: a map equal to a balanced map;
  * `Balanced.of_equiv`, `Balanced.of_bijective`, `Balanced.id`: bijections;
  * `Balanced.fst`, `Balanced.snd`: the projections of a product;
  * `Balanced.comp`: compositions;
  * `Balanced.prodMap`: products of maps;
  * `Balanced.prodMk_const`: pairing with an element of a one-element type;
  * `Balanced.postcomp`: a balanced map applied to every value of a function;
  * `Balanced.precomp_injective`: the restriction of a function to distinct
    indices; `Balanced.eval`: its value at one index;
  * `Balanced.finConsSplit`: a tuple split into its head and its tail;
  * `Balanced.finMod`: the reduction of a number below `2 ^ w` to `b` bits.
* `FractionLE.comap`: a fraction bound on `β` is a fraction bound on `α`.

No probability appears here; `FractionLE` counts.
-/

namespace CertiFri.Oracle

/-- `f` is a projection up to a bijection: there is a finite type `γ` and a
bijection of `α` with `β × γ` whose first component is `f`. -/
def Balanced {α β : Type} (f : α → β) : Prop :=
  ∃ (γ : Type) (_ : Fintype γ) (e : α ≃ β × γ), ∀ a, (e a).1 = f a

namespace Balanced

variable {α β γ α' β' ι κ : Type}

/-- A map that agrees with a balanced map is balanced. -/
theorem congr {f g : α → β} (hf : Balanced f) (h : ∀ a, f a = g a) : Balanced g := by
  obtain ⟨δ, hδ, e, he⟩ := hf
  exact ⟨δ, hδ, e, fun a => (he a).trans (h a)⟩

/-- A bijection, given as an equivalence, is balanced. -/
theorem of_equiv (e : α ≃ β) : Balanced e :=
  ⟨PUnit, inferInstance, e.trans (Equiv.prodPUnit β).symm, fun _ => rfl⟩

/-- A bijection is balanced. -/
theorem of_bijective {f : α → β} (hf : Function.Bijective f) : Balanced f :=
  of_equiv (Equiv.ofBijective f hf)

/-- The identity is balanced. -/
protected theorem id : Balanced (id : α → α) :=
  of_equiv (Equiv.refl α)

/-- The first projection of a product with a finite type is balanced. -/
theorem fst [Finite γ] : Balanced (Prod.fst : β × γ → β) :=
  ⟨γ, Fintype.ofFinite γ, Equiv.refl _, fun _ => rfl⟩

/-- The second projection of a product with a finite type is balanced. -/
theorem snd [Finite β] : Balanced (Prod.snd : β × γ → γ) :=
  ⟨β, Fintype.ofFinite β, Equiv.prodComm β γ, fun _ => rfl⟩

/-- A composition of balanced maps is balanced. -/
theorem comp {g : β → γ} {f : α → β} (hg : Balanced g) (hf : Balanced f) : Balanced (g ∘ f) := by
  obtain ⟨δ, _, e, he⟩ := hf
  obtain ⟨δ', _, e', he'⟩ := hg
  refine ⟨δ' × δ, inferInstance,
    e.trans ((e'.prodCongr (Equiv.refl δ)).trans (Equiv.prodAssoc γ δ' δ)), fun a => ?_⟩
  simp [← he, ← he']

/-- The product of two balanced maps is balanced. -/
theorem prodMap {f : α → β} {g : α' → β'} (hf : Balanced f) (hg : Balanced g) :
    Balanced (Prod.map f g) := by
  obtain ⟨δ, _, e, he⟩ := hf
  obtain ⟨δ', _, e', he'⟩ := hg
  refine ⟨δ × δ', inferInstance,
    (e.prodCongr e').trans (Equiv.prodProdProdComm β δ β' δ'), fun a => ?_⟩
  exact Prod.ext (he a.1) (he' a.2)

/-- Pairing a balanced map with an element of a one-element type is balanced. -/
theorem prodMk_const [Subsingleton γ] (c : γ) {f : α → β} (hf : Balanced f) :
    Balanced (fun a => (c, f a)) := by
  have : Unique γ := uniqueOfSubsingleton c
  exact (of_equiv (Equiv.uniqueProd β γ).symm).comp hf |>.congr fun a =>
    Prod.ext (Subsingleton.elim _ _) rfl

/-- A balanced map applied to every value of a function on a finite type is a
balanced map of the functions. -/
theorem postcomp [Finite ι] {f : α → β} (hf : Balanced f) :
    Balanced (fun (u : ι → α) (i : ι) => f (u i)) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨δ, _, e, he⟩ := hf
  refine ⟨ι → δ, inferInstance,
    (Equiv.piCongrRight fun _ => e).trans (Equiv.arrowProdEquivProdArrow ι _ _), fun u => ?_⟩
  funext i
  exact he (u i)

/-- Restricting the functions on a finite type to distinct indices is balanced. -/
theorem precomp_injective [Finite ι] [Finite α] {g : κ → ι} (hg : Function.Injective g) :
    Balanced (fun (u : ι → α) (k : κ) => u (g k)) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite α
  refine ⟨{ i // i ∉ Set.range g } → α, inferInstance,
    (Equiv.piEquivPiSubtypeProd (· ∈ Set.range g) fun _ => α).trans
      ((Equiv.arrowCongr (Equiv.ofInjective g hg).symm (Equiv.refl α)).prodCongr (Equiv.refl _)),
    fun u => ?_⟩
  funext k
  simp [Equiv.arrowCongr]

/-- The value at one index of the functions on a finite type is balanced. -/
theorem eval [Finite ι] [Finite α] (i : ι) : Balanced (fun u : ι → α => u i) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite α
  exact ⟨{ j // j ≠ i } → α, inferInstance, Equiv.funSplitAt i α, fun _ => rfl⟩

/-- Splitting a tuple into its first entry and the others is balanced. -/
theorem finConsSplit (n : ℕ) :
    Balanced (fun u : Fin (n + 1) → α => (u 0, fun i : Fin n => u i.succ)) :=
  (of_equiv (Fin.consEquiv fun _ => α).symm).congr fun _ => rfl

/-- Reducing the numbers below `2 ^ w` to `b ≤ w` bits is balanced. -/
theorem finMod {w b : ℕ} (h : b ≤ w) :
    Balanced (fun x : Fin (2 ^ w) =>
      (⟨(x : ℕ) % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩ : Fin (2 ^ b))) := by
  have hw : 2 ^ w = 2 ^ (w - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel h]
  refine ⟨Fin (2 ^ (w - b)), inferInstance,
    (finCongr hw).trans (finProdFinEquiv.symm.trans (Equiv.prodComm _ _)), fun x => ?_⟩
  exact Fin.ext rfl

end Balanced

/-- **A fraction bound moves along a balanced map.** If at most a fraction `ε`
of `β` satisfies `p`, at most a fraction `ε` of `α` is mapped into `p`. -/
theorem FractionLE.comap {α β : Type} [Fintype α] [Fintype β] {f : α → β} (hf : Balanced f)
    {p : β → Prop} {ε : ℝ} (h : FractionLE p ε) : FractionLE (fun a => p (f a)) ε := by
  obtain ⟨γ, _, e, he⟩ := hf
  obtain ⟨B, hB, hp⟩ := h
  refine ⟨(B ×ˢ (Finset.univ : Finset γ)).map e.symm.toEmbedding, ?_, fun a ha => ?_⟩
  · rw [Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_congr e,
      Fintype.card_prod, Nat.cast_mul, Nat.cast_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _)
  · refine Finset.mem_map.mpr ⟨e a, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩,
      e.symm_apply_apply a⟩
    rw [he]
    exact hp _ ha

end CertiFri.Oracle
