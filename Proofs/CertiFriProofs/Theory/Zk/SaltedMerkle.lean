import CertiFriProofs.Theory.Oracle.Prob
import CertiFriProofs.Theory.Oracle.BadEvent
import CertiFriProofs.Theory.Zk.PolyBlinding

/-!
# Salted Merkle Leaf Hiding in the Classical Random Oracle Model

This module proves statistical indistinguishability (hiding) of unopened salted
Merkle leaves in the classical random oracle model (`CertiFri.Oracle.OracleComp`),
modeling both position-separated leaf hashing `RO(idx || row || salt)` and the
unindexed leaf hashing `RO(row || salt)` used in `multi-stark/v6-zk` (`zk.rs`).

## Main Results

1. **Identical-Until-Bad Game-Playing Framework for `OracleComp` (`IdenticalUntilBad`):**
   * `abs_prob_sub_prob_le_prob_hit`: if two oracle logs `l₁, l₂` agree outside a
     finite hidden query set `S` and `l₂` has no entries in `S`, then any adaptive
     distinguisher `c : OracleComp Y Bool` has distinguishing advantage bounded by
     the probability that `c` queries an element of `S` when run from `l₂`.
   * `abs_expect_sub_expect_le_of_noQueryIn`: preserves the coupling across any
     intermediate phase (`buildMerkleTree`) whose queries are disjoint from `S`.

2. **Batch Fresh-Query Evaluation & Uniform-Salt Hit Bound (`SaltHitBound`):**
   * `expect_queryFin_of_fresh`: querying the ROM on `m` pairwise-distinct fresh
     inputs is identically distributed to sampling `m` independent uniform digests
     and logging them.
   * `unifAvg_prob_hit_le`: for any `N_RO`-query adaptive distinguisher whose view
     is independent of the unopened salts, the probability of hitting any of the
     `L_unopened` unopened salted leaf queries is at most `N_RO * L_unopened / |Salt|`.

3. **Salted Merkle Unopened Leaf Hiding (`SaltedMerkleHiding`):**
   * `salted_leaf_rom_indistinguishable`: for any `L` leaves, any secret rows
     `rows : Fin L → Row`, any opened index set `opened : Finset (Fin L)` with
     `L_unopened = (Finset.univ \ opened).card`, and any `N_RO`-query adaptive
     distinguisher receiving the opened rows, opened salts, and the full Merkle
     tree (including root/cap, all sibling hashes, and all unopened leaf digests),
     the distinguishing advantage against the witness-free ideal game (which
     samples uniformly random digests for all unopened leaves) is at most
     **`N_RO * L_unopened / |Salt|`**.
   * `salted_leaf_rom_indistinguishable_two_rows`: two secret row vectors agreeing
     on `opened` have distinguishing advantage `≤ 2 * N_RO * L_unopened / |Salt|`.
   * `salted_leaf_unindexed_rom_indistinguishable`: in the unindexed `RO(row || salt)`
     model (matching `multi-stark/v6-zk`'s `hash_leaf_rows_with_salt`), the
     distinguishing advantage is at most
     **`(N_RO * L_unopened + L_unopened * (L - 1)) / |Salt|`**.

4. **Concrete Salt-Size Instantiations (`ConcreteSalts`):**
   * **16-byte (`s = 128`-bit) classical salt** (`Fin (2 ^ 128)`, matching `v6-zk`
     default `ZK_LEAF_SALT_BYTES = 16`): advantage `≤ N_RO * L_unopened / 2 ^ 128`.
   * **32-byte (`s = 256`-bit) post-quantum-margin salt** (`Fin (2 ^ 256)`):
     advantage `≤ N_RO * L_unopened / 2 ^ 256`.
   * Explicit classical and Grover cardinality-ratio tradeoff lemmas between
     128-bit and 256-bit salts (the ROM proofs here are strictly classical).
-/

namespace CertiFri.Zk

open CertiFri.Oracle CertiFri.Oracle.OracleComp
open scoped BigOperators

/-! ## Section 1: Identical-Until-Bad Game-Playing Coupling for `OracleComp` -/

section IdenticalUntilBad

universe u v w

variable {X : Type u} {Y : X → Type v} [DecidableEq X]

/-- Two oracle logs agree on every query outside the hidden set `S`. -/
def LogsAgreeOutside (S : Finset X) (l₁ l₂ : Log Y) : Prop :=
  ∀ x : X, x ∉ S → l₁.dlookup x = l₂.dlookup x

/-- An oracle log contains no entries for any query in `S`. -/
def LogsFreshOn (S : Finset X) (l : Log Y) : Prop :=
  ∀ x ∈ S, l.dlookup x = none

/-- An oracle computation never queries any element of `S` on any execution path. -/
def NoQueryIn {α : Type w} (S : Finset X) : OracleComp Y α → Prop
  | .pure _ => True
  | .queryBind x k => x ∉ S ∧ ∀ y, NoQueryIn S (k y)

theorem dlookup_append_singleton_of_ne {l : Log Y} {x z : X} {y : Y x}
    (hl : l.dlookup z = none) (hne : z ≠ x) :
    (l ++ [(⟨x, y⟩ : Sigma Y)]).dlookup z = none := by
  rw [List.dlookup_append, hl, Option.none_or]
  exact List.dlookup_cons_ne [] ⟨x, y⟩ hne

theorem logsAgreeOutside_append_singleton {S : Finset X} {l₁ l₂ : Log Y}
    (hAgree : LogsAgreeOutside S l₁ l₂) {x : X} (y : Y x) :
    LogsAgreeOutside S (l₁ ++ [⟨x, y⟩]) (l₂ ++ [⟨x, y⟩]) := by
  intro z hz
  rw [List.dlookup_append, List.dlookup_append, hAgree z hz]

theorem logsFreshOn_append_singleton {S : Finset X} {l : Log Y}
    (hFresh : LogsFreshOn S l) {x : X} (hx : x ∉ S) (y : Y x) :
    LogsFreshOn S (l ++ [⟨x, y⟩]) := fun z hz =>
  dlookup_append_singleton_of_ne (hFresh z hz) (fun h => hx (h ▸ hz))

omit [DecidableEq X] in
theorem noQueryIn_bind {α β : Type w} {S : Finset X} {c : OracleComp Y α}
    {g : α → OracleComp Y β} (hc : NoQueryIn S c) (hg : ∀ a, NoQueryIn S (g a)) :
    NoQueryIn S (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | queryBind x k ih => exact ⟨hc.1, fun y => ih y (hc.2 y)⟩

theorem dlookup_none_of_noQueryIn {α : Type w} {c : OracleComp Y α} {x : X}
    (hNoX : NoQueryIn {x} c) {l l' : Log Y} {a : α} (hout : Outcome c l a l')
    (hl : l.dlookup x = none) : l'.dlookup x = none := by
  induction c generalizing l with
  | pure a₀ => exact hout.2.symm ▸ hl
  | queryBind q k ih =>
    have hne : x ≠ q := fun h => hNoX.1 (by simp [h])
    cases hq : l.dlookup q with
    | some y =>
      exact ih y (hNoX.2 y) ((outcome_queryBind_of_lookup hq k a l').mp hout) hl
    | none =>
      obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hq k a l').mp hout
      exact ih y (hNoX.2 y) hy (dlookup_append_singleton_of_ne hl hne)

theorem expect_sum {ι : Type*} {α : Type w} [∀ x, Fintype (Y x)]
    (s : Finset ι) (f : ι → α → Log Y → ℝ) (c : OracleComp Y α) (l : Log Y) :
    expect (fun a l' => ∑ i ∈ s, f i a l') c l = ∑ i ∈ s, expect (f i) c l := by
  induction c generalizing l with
  | pure a => rfl
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y =>
      simp only [expect_queryBind_of_lookup hx, ih]
    | none =>
      simp only [expect_queryBind_of_fresh hx, ih, Finset.sum_div]
      rw [Finset.sum_comm]

theorem expect_div_const {α : Type w} [∀ x, Fintype (Y x)]
    (f : α → Log Y → ℝ) (d : ℝ) (c : OracleComp Y α) (l : Log Y) :
    expect (fun a l' => f a l' / d) c l = expect f c l / d := by
  simp_rw [div_eq_mul_inv, mul_comm _ d⁻¹, expect_const_mul]

theorem abs_expect_sub_expect_le {α : Type w} [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)]
    (f g : α → Log Y → ℝ) (c : OracleComp Y α) (l : Log Y) :
    |expect f c l - expect g c l| ≤ expect (fun a l' => |f a l' - g a l'|) c l := by
  induction c generalizing l with
  | pure a => exact le_rfl
  | queryBind x k ih =>
    cases hl : l.dlookup x with
    | some y =>
      rw [expect_queryBind_of_lookup hl, expect_queryBind_of_lookup hl,
        expect_queryBind_of_lookup hl]
      exact ih y _
    | none =>
      rw [expect_queryBind_of_fresh hl, expect_queryBind_of_fresh hl,
        expect_queryBind_of_fresh hl]
      have hcard : (0 : ℝ) < Fintype.card (Y x) := Nat.cast_pos.mpr Fintype.card_pos
      rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard]
      refine div_le_div_of_nonneg_right ?_ hcard.le
      exact (Finset.abs_sum_le_sum_abs
        (f := fun y : Y x => expect f (k y) (l ++ [⟨x, y⟩]) - expect g (k y) (l ++ [⟨x, y⟩]))
        Finset.univ).trans (Finset.sum_le_sum fun y _ => ih y _)

/-- **Fundamental Identical-Until-Bad Lemma for `OracleComp`:**
if logs `l₁, l₂` agree outside `S` and `l₂` is fresh on `S`, then any adaptive
distinguisher `c : OracleComp Y Bool` distinguishes `l₁` from `l₂` by at most
the probability that `c` queries some `x ∈ S` when run from `l₂`. -/
theorem abs_prob_sub_prob_le_prob_hit [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)]
    (S : Finset X) (c : OracleComp Y Bool) {l₁ l₂ : Log Y}
    (hAgree : LogsAgreeOutside S l₁ l₂) (hFresh : LogsFreshOn S l₂) :
    |prob (fun b _ => b = true) c l₁ - prob (fun b _ => b = true) c l₂| ≤
      prob (fun _ l' => ∃ x ∈ S, (l'.dlookup x).isSome) c l₂ := by
  induction c generalizing l₁ l₂ with
  | pure b =>
    rw [prob_pure, prob_pure, sub_self, abs_zero]
    exact prob_nonneg _ _ _
  | queryBind x k ih =>
    by_cases hx : x ∈ S
    · have hfresh_x : l₂.dlookup x = none := hFresh x hx
      have hhit1 : prob (fun _ l' => ∃ z ∈ S, (l'.dlookup z).isSome) (.queryBind x k) l₂ = 1 := by
        refine prob_eq_one_of_outcome fun a l' hout => ?_
        obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hfresh_x k a l').mp hout
        have hdl : (l₂ ++ [(⟨x, y⟩ : Sigma Y)]).dlookup x = some y := by
          rw [List.dlookup_append, hfresh_x, Option.none_or, List.dlookup_cons_eq]
        have hdl' : l'.dlookup x = some y := dlookup_of_prefix hdl hy.prefix
        exact ⟨x, hx, by simp [hdl']⟩
      rw [hhit1]
      have hp1_0 := prob_nonneg (fun b _ => b = true) (.queryBind x k) l₁
      have hp1_1 := prob_le_one (fun b _ => b = true) (.queryBind x k) l₁
      have hp2_0 := prob_nonneg (fun b _ => b = true) (.queryBind x k) l₂
      have hp2_1 := prob_le_one (fun b _ => b = true) (.queryBind x k) l₂
      rw [abs_le]
      constructor <;> linarith
    · have hl_eq : l₁.dlookup x = l₂.dlookup x := hAgree x hx
      cases hl₂ : l₂.dlookup x with
      | some y =>
        have hl₁ : l₁.dlookup x = some y := hl_eq.trans hl₂
        rw [prob_queryBind_of_lookup hl₁, prob_queryBind_of_lookup hl₂,
          prob_queryBind_of_lookup hl₂]
        exact ih y hAgree hFresh
      | none =>
        have hl₁ : l₁.dlookup x = none := hl_eq.trans hl₂
        rw [prob_queryBind_of_fresh hl₁, prob_queryBind_of_fresh hl₂,
          prob_queryBind_of_fresh hl₂]
        have hcard : (0 : ℝ) < Fintype.card (Y x) := Nat.cast_pos.mpr Fintype.card_pos
        rw [← sub_div, abs_div, abs_of_pos hcard, ← Finset.sum_sub_distrib]
        refine div_le_div_of_nonneg_right ?_ hcard.le
        have habs := Finset.abs_sum_le_sum_abs
          (f := fun y : Y x => prob (fun b _ => b = true) (k y) (l₁ ++ [⟨x, y⟩]) -
            prob (fun b _ => b = true) (k y) (l₂ ++ [⟨x, y⟩])) Finset.univ
        exact habs.trans (Finset.sum_le_sum fun y _ =>
          ih y (logsAgreeOutside_append_singleton hAgree y)
            (logsFreshOn_append_singleton hFresh hx y))

/-- **Disjoint-Phase Coupling Lemma:** if `phase` makes no queries in `S` (`NoQueryIn S phase`),
then `LogsAgreeOutside S` and `LogsFreshOn S` are preserved along every branch of `phase`,
and any pointwise bound on continuation expectations lifts directly through `phase`. -/
theorem abs_expect_sub_expect_le_of_noQueryIn {α : Type w}
    [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)]
    (S : Finset X) (phase : OracleComp Y α) (hNo : NoQueryIn S phase)
    (g₁ g₂ h : α → Log Y → ℝ) {l₁ l₂ : Log Y}
    (hAgree : LogsAgreeOutside S l₁ l₂) (hFresh : LogsFreshOn S l₂)
    (hstep : ∀ a l₁' l₂', LogsAgreeOutside S l₁' l₂' → LogsFreshOn S l₂' →
      |g₁ a l₁' - g₂ a l₂'| ≤ h a l₂') :
    |expect g₁ phase l₁ - expect g₂ phase l₂| ≤ expect h phase l₂ := by
  induction phase generalizing l₁ l₂ with
  | pure a =>
    exact hstep a l₁ l₂ hAgree hFresh
  | queryBind x k ih =>
    obtain ⟨hx, hk⟩ := hNo
    have hl_eq : l₁.dlookup x = l₂.dlookup x := hAgree x hx
    cases hl₂ : l₂.dlookup x with
    | some y =>
      have hl₁ : l₁.dlookup x = some y := hl_eq.trans hl₂
      rw [expect_queryBind_of_lookup hl₁, expect_queryBind_of_lookup hl₂,
        expect_queryBind_of_lookup hl₂]
      exact ih y (hk y) hAgree hFresh
    | none =>
      have hl₁ : l₁.dlookup x = none := hl_eq.trans hl₂
      rw [expect_queryBind_of_fresh hl₁, expect_queryBind_of_fresh hl₂,
        expect_queryBind_of_fresh hl₂]
      have hcard : (0 : ℝ) < Fintype.card (Y x) := Nat.cast_pos.mpr Fintype.card_pos
      rw [← sub_div, abs_div, abs_of_pos hcard, ← Finset.sum_sub_distrib]
      refine div_le_div_of_nonneg_right ?_ hcard.le
      have habs := Finset.abs_sum_le_sum_abs
        (f := fun y : Y x => expect g₁ (k y) (l₁ ++ [⟨x, y⟩]) - expect g₂ (k y) (l₂ ++ [⟨x, y⟩]))
        Finset.univ
      exact habs.trans (Finset.sum_le_sum fun y _ =>
        ih y (hk y) (logsAgreeOutside_append_singleton hAgree y)
          (logsFreshOn_append_singleton hFresh hx y))

end IdenticalUntilBad

/-! ## Section 2: Batch Fresh Queries & Uniform-Salt Hit Bound -/

section SaltHitBound

/-- Query a constant-answer ROM on a `Fin m`-indexed tuple of inputs. -/
def queryFin {X Digest : Type} :
    {m : ℕ} → (Fin m → X) → OracleComp (fun _ : X => Digest) (Fin m → Digest)
  | 0, _ => .pure Fin.elim0
  | _ + 1, q =>
    .queryBind (q 0) fun d₀ =>
      (queryFin (fun i => q i.succ)).bind fun ds =>
        .pure (Fin.cons d₀ ds)

/-- A query not appearing in `q` remains fresh after running `queryFin q`. -/
theorem dlookup_none_of_outcome_queryFin {X Digest : Type} [DecidableEq X] :
    ∀ {k : ℕ} (q : Fin k → X) {l l' : Log (fun _ : X => Digest)} {res : Fin k → Digest},
      Outcome (queryFin q) l res l' →
      ∀ x, (∀ i, q i ≠ x) → l.dlookup x = none → l'.dlookup x = none
  | 0, _, _, _, _, hout, _, _, hl => hout.2.symm ▸ hl
  | _ + 1, q, l, l', res, hout, x, hne, hl => by
    simp only [queryFin] at hout
    cases h0 : l.dlookup (q 0) with
    | some d₀ =>
      rw [outcome_queryBind_of_lookup h0] at hout
      obtain ⟨ds, l'', h1, h2⟩ := outcome_bind.mp hout
      rw [outcome_pure] at h2
      rw [h2.2]
      exact dlookup_none_of_outcome_queryFin _ h1 x (fun i => hne i.succ) hl
    | none =>
      rw [outcome_queryBind_of_fresh h0] at hout
      obtain ⟨d₀, hout'⟩ := hout
      obtain ⟨ds, l'', h1, h2⟩ := outcome_bind.mp hout'
      rw [outcome_pure] at h2
      rw [h2.2]
      exact dlookup_none_of_outcome_queryFin _ h1 x (fun i => hne i.succ)
        (dlookup_append_singleton_of_ne hl (hne 0).symm)

/-- Querying the ROM on `m` pairwise-distinct fresh inputs is identically distributed to
sampling `ds : Fin m → Digest` uniformly and appending `[⟨q i, ds i⟩]` to the log. -/
theorem expect_queryFin_of_fresh {X Digest : Type} [DecidableEq X] [Fintype Digest] [Nonempty Digest]
    {m : ℕ} (q : Fin m → X) (hq : Function.Injective q)
    (l : Log (fun _ : X => Digest)) (hFresh : ∀ i : Fin m, l.dlookup (q i) = none)
    (F : (Fin m → Digest) → Log (fun _ : X => Digest) → ℝ) :
    expect F (queryFin q) l =
      (∑ ds : Fin m → Digest, F ds (l ++ List.ofFn fun i : Fin m => ⟨q i, ds i⟩)) /
        (Fintype.card (Fin m → Digest) : ℝ) := by
  induction m generalizing l with
  | zero =>
    have hsum : ∑ ds : Fin 0 → Digest,
        F ds (l ++ List.ofFn fun i : Fin 0 => ⟨q i, ds i⟩) = F Fin.elim0 l := by
      have huniv : (Finset.univ : Finset (Fin 0 → Digest)) = {Fin.elim0} := by
        ext f
        simp [funext_iff]
      rw [huniv, Finset.sum_singleton]
      simp
    have hcard : (Fintype.card (Fin 0 → Digest) : ℝ) = 1 := by simp
    rw [hsum, hcard, div_one]
    rfl
  | succ m ih =>
    have h0 : l.dlookup (q 0) = none := hFresh 0
    simp only [queryFin]
    rw [expect_queryBind_of_fresh h0]
    have hinner : ∀ d₀ : Digest,
        expect (fun ds l' => F (Fin.cons d₀ ds) l')
          (queryFin (fun i : Fin m => q i.succ)) (l ++ [⟨q 0, d₀⟩]) =
        (∑ ds : Fin m → Digest,
          F (Fin.cons d₀ ds) (l ++ List.ofFn fun i : Fin (m + 1) =>
            ⟨q i, (Fin.cons d₀ ds : Fin (m + 1) → Digest) i⟩)) /
          (Fintype.card (Fin m → Digest) : ℝ) := by
      intro d₀
      have hq' : Function.Injective (fun i : Fin m => q i.succ) :=
        fun i j hij => Fin.succ_injective m (hq hij)
      have hFresh' : ∀ i : Fin m, (l ++ [(⟨q 0, d₀⟩ : Sigma (fun _ : X => Digest))]).dlookup
          (q i.succ) = none := fun i =>
        dlookup_append_singleton_of_ne (hFresh i.succ) (fun h => Fin.succ_ne_zero i (hq h))
      have hih := ih (fun i => q i.succ) hq' (l ++ [⟨q 0, d₀⟩]) hFresh'
        (fun ds l' => F (Fin.cons d₀ ds) l')
      rw [hih]
      congr 1
      refine Finset.sum_congr rfl fun ds _ => ?_
      rw [List.ofFn_succ, List.append_assoc, List.singleton_append]
      rfl
    have hbind : ∀ d₀ : Digest,
        expect F ((queryFin (fun i : Fin m => q i.succ)).bind fun ds => .pure (Fin.cons d₀ ds))
          (l ++ [⟨q 0, d₀⟩]) =
        expect (fun ds l' => F (Fin.cons d₀ ds) l')
          (queryFin (fun i : Fin m => q i.succ)) (l ++ [⟨q 0, d₀⟩]) := fun d₀ => by
      rw [expect_bind]
      rfl
    simp_rw [hbind, hinner]
    rw [← Finset.sum_div, div_div, ← Nat.cast_mul]
    have hcard : Fintype.card (Fin m → Digest) * Fintype.card Digest =
        Fintype.card (Fin (m + 1) → Digest) := by
      simp [pow_succ]
    rw [hcard]
    congr 1
    let e : Digest × (Fin m → Digest) ≃ (Fin (m + 1) → Digest) :=
      (Fin.consEquiv (fun _ : Fin (m + 1) => Digest))
    have hsum_eq :
        ∑ d₀ : Digest, ∑ ds : Fin m → Digest,
          F (Fin.cons d₀ ds) (l ++ List.ofFn fun i : Fin (m + 1) =>
            ⟨q i, (Fin.cons d₀ ds : Fin (m + 1) → Digest) i⟩) =
        ∑ p : Digest × (Fin m → Digest),
          F (e p) (l ++ List.ofFn fun i : Fin (m + 1) => ⟨q i, e p i⟩) := by
      rw [Fintype.sum_prod_type]
      rfl
    rw [hsum_eq]
    exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Counting lemma for a single hidden salt slot: given a log suffix `t` of length `≤ N_RO`
and an injective encoding `mkQ : Salt → X`, at most `t.length` salts `s : Salt` satisfy
`(t.dlookup (mkQ s)).isSome`. -/
theorem card_salt_hits_le {X Digest Salt : Type} [DecidableEq X] [Fintype Salt]
    (mkQ : Salt → X) (hmkQ : Function.Injective mkQ) (t : Log (fun _ : X => Digest)) :
    (Finset.univ.filter fun s : Salt => (t.dlookup (mkQ s)).isSome).card ≤ t.length := by
  have hsub :
      (Finset.univ.filter fun s : Salt => (t.dlookup (mkQ s)).isSome).image mkQ ⊆
        t.keys.toFinset := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    have hsome : (t.dlookup (mkQ s)).isSome := (Finset.mem_filter.mp hs).2
    rw [Option.isSome_iff_exists] at hsome
    obtain ⟨y, hy⟩ := hsome
    exact List.mem_toFinset.mpr (List.dlookup_isSome.mp (by simp [hy]))
  calc (Finset.univ.filter fun s : Salt => (t.dlookup (mkQ s)).isSome).card
      = ((Finset.univ.filter fun s : Salt => (t.dlookup (mkQ s)).isSome).image mkQ).card :=
        (Finset.card_image_of_injective _ hmkQ).symm
    _ ≤ t.keys.toFinset.card := Finset.card_le_card hsub
    _ ≤ t.keys.length := List.toFinset_card_le t.keys
    _ = t.length := by simp [List.keys]

/-- Helper: coordinate projection `salts ↦ salts i` is a uniform pushforward onto `Salt`. -/
theorem isUniformPushforward_proj_fin {m : ℕ} {Salt : Type} [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] (i : Fin m) :
    IsUniformPushforward (fun salts : Fin m → Salt => salts i) := by
  refine isUniformPushforward_of_const_filter_card _ ((Fintype.card Salt) ^ (m - 1)) fun s => ?_
  let e : {salts : Fin m → Salt // salts i = s} ≃ ({j : Fin m // j ≠ i} → Salt) :=
    { toFun := fun ⟨f, _⟩ j => f j.1
      invFun := fun g => ⟨fun j => if h : j = i then s else g ⟨j, h⟩, by simp⟩
      left_inv := fun ⟨f, hf⟩ => by
        apply Subtype.ext
        funext j
        dsimp only
        split_ifs with h
        · subst h; exact hf.symm
        · rfl
      right_inv := fun g => by
        funext ⟨j, hj⟩
        simp [hj] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun]
  have hsub_card : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  rw [hsub_card]

/-- Helper: for a fixed log suffix `t` of length `≤ N_RO`, the average over uniform salts
`salts : Fin m → Salt` of hitting `mkQ i (salts i)` in `t` is at most `N_RO / |Salt|`. -/
theorem avg_hit_suffix_single_le {X Digest Salt : Type} [DecidableEq X] [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] {m N_RO : ℕ}
    (mkQ : Fin m → Salt → X) (hmkQ : ∀ i, Function.Injective (mkQ i))
    (t : Log (fun _ : X => Digest)) (htlen : t.length ≤ N_RO) (i : Fin m) :
    (∑ salts : Fin m → Salt,
        if (t.dlookup (mkQ i (salts i))).isSome then (1 : ℝ) else 0) /
      (Fintype.card (Fin m → Salt) : ℝ) ≤ (N_RO : ℝ) / (Fintype.card Salt : ℝ) := by
  have hEq :
      (∑ salts : Fin m → Salt,
        if (t.dlookup (mkQ i (salts i))).isSome then (1 : ℝ) else 0) /
      (Fintype.card (Fin m → Salt) : ℝ) =
      unifProb (fun salts : Fin m → Salt => salts i)
        (fun s : Salt => (t.dlookup (mkQ i s)).isSome) := by
    unfold unifProb
    congr 1
    refine Finset.sum_congr rfl fun salts _ => by
      by_cases h : (t.dlookup (mkQ i (salts i))).isSome = true <;> simp [h]
  rw [hEq, unifProb_eq_unifExpect, unifExpect_eq_sum_unifMass]
  have hunif : ∀ s : Salt,
      unifMass (fun salts : Fin m → Salt => salts i) s = 1 / (Fintype.card Salt : ℝ) :=
    isUniformPushforward_proj_fin i
  simp_rw [hunif]
  rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
  have hsum : (∑ s : Salt, @ite _ ((t.dlookup (mkQ i s)).isSome = true) (Classical.propDecidable _)
      (1 : ℝ) 0) = ((Finset.univ.filter fun s : Salt => (t.dlookup (mkQ i s)).isSome).card : ℝ) := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun s _ => by
      by_cases h : (t.dlookup (mkQ i s)).isSome = true <;> simp [h]
  rw [hsum]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast (card_salt_hits_le (mkQ i) (hmkQ i) t).trans htlen

/-- **Uniform-Salt Hit Bound (`unifAvg_prob_hit_le`):**
for ANY fixed `N_RO`-query oracle computation `c : OracleComp (fun _ => Digest) Bool`,
ANY starting log `l₂` containing NO queries of the form `mkQ i s` (`i : Fin m`, `s : Salt`),
where each `mkQ i : Salt → X` is injective, the average over uniform independent salts
`salts : Fin m → Salt` of the probability that `c` hits `{mkQ i (salts i) | i : Fin m}`
is at most **`(N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ)`**. -/
theorem unifAvg_prob_hit_le {X Digest Salt : Type}
    [DecidableEq X] [DecidableEq Salt] [Fintype Digest] [Nonempty Digest]
    [Fintype Salt] [Nonempty Salt]
    {m N_RO : ℕ} (mkQ : Fin m → Salt → X) (hmkQ : ∀ i, Function.Injective (mkQ i))
    (c : OracleComp (fun _ : X => Digest) Bool) (hc : c.QueryBound N_RO)
    (l₂ : Log (fun _ : X => Digest)) (hFresh : ∀ (i : Fin m) (s : Salt), l₂.dlookup (mkQ i s) = none) :
    (∑ salts : Fin m → Salt,
        prob (fun _ l' => ∃ i : Fin m, (l'.dlookup (mkQ i (salts i))).isSome) c l₂) /
      (Fintype.card (Fin m → Salt) : ℝ) ≤
      (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
  classical
  unfold prob
  rw [← expect_sum, ← expect_div_const]
  refine expect_le_of_outcome fun _ l' hout => ?_
  obtain ⟨t, rfl, htlen⟩ := hout.exists_append hc
  have hstep :
      (∑ salts : Fin m → Salt,
        @ite _ (∃ i : Fin m, ((l₂ ++ t).dlookup (mkQ i (salts i))).isSome)
          (Classical.propDecidable _) (1 : ℝ) 0) ≤
      ∑ i : Fin m, ∑ salts : Fin m → Salt,
        if (t.dlookup (mkQ i (salts i))).isSome then (1 : ℝ) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun salts _ => ?_
    by_cases hex : ∃ i : Fin m, ((l₂ ++ t).dlookup (mkQ i (salts i))).isSome
    · rw [ite_eq_left hex]
      obtain ⟨i₀, hi₀⟩ := hex
      have hi₀' : (t.dlookup (mkQ i₀ (salts i₀))).isSome := by
        rw [List.dlookup_append, hFresh i₀ (salts i₀), Option.none_or] at hi₀
        exact hi₀
      have hle := Finset.single_le_sum
        (f := fun i : Fin m => if (t.dlookup (mkQ i (salts i))).isSome then (1 : ℝ) else 0)
        (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ i₀)
      simpa [hi₀'] using hle
    · rw [ite_eq_right hex]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hcard_pos : (0 : ℝ) < Fintype.card (Fin m → Salt) := Nat.cast_pos.mpr Fintype.card_pos
  calc (∑ salts : Fin m → Salt,
          @ite _ (∃ i : Fin m, ((l₂ ++ t).dlookup (mkQ i (salts i))).isSome)
            (Classical.propDecidable _) (1 : ℝ) 0) /
        (Fintype.card (Fin m → Salt) : ℝ)
      ≤ (∑ i : Fin m, ∑ salts : Fin m → Salt,
          if (t.dlookup (mkQ i (salts i))).isSome then (1 : ℝ) else 0) /
        (Fintype.card (Fin m → Salt) : ℝ) :=
        div_le_div_of_nonneg_right hstep hcard_pos.le
    _ = ∑ i : Fin m, (∑ salts : Fin m → Salt,
          if (t.dlookup (mkQ i (salts i))).isSome then (1 : ℝ) else 0) /
        (Fintype.card (Fin m → Salt) : ℝ) := Finset.sum_div _ _ _
    _ ≤ ∑ _i : Fin m, ((N_RO : ℝ) / (Fintype.card Salt : ℝ)) :=
        Finset.sum_le_sum fun i _ => avg_hit_suffix_single_le mkQ hmkQ t htlen i
    _ = (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring

end SaltHitBound

/-! ## Section 3: Salted Merkle Tree Model & Unopened Leaf Hiding in the ROM -/

section SaltedMerkleHiding

/-- Domain-separated ROM query type for a position-separated salted Merkle tree:
salted leaf queries `RO(.leaf idx row salt)` and 2-to-1 internal compressions
`RO(.compress left right)` are strictly disjoint. -/
inductive SaltedMerkleQuery (L : ℕ) (Row Salt Digest : Type) where
  | leaf (idx : Fin L) (row : Row) (salt : Salt)
  | compress (left right : Digest)
  deriving DecidableEq

/-- Every query to the salted Merkle ROM returns a uniform digest in `Digest`. -/
abbrev SaltedMerkleAns (L : ℕ) (Row Salt Digest : Type) :
    SaltedMerkleQuery L Row Salt Digest → Type := fun _ => Digest

/-- Compress one layer of Merkle digests pairwise via `RO(.compress left right)`. -/
def compressMerkleLayer {L : ℕ} {Row Salt Digest : Type} :
    List Digest → OracleComp (SaltedMerkleAns L Row Salt Digest) (List Digest)
  | [] => .pure []
  | [d] => .pure [d]
  | l :: r :: rest =>
    .queryBind (.compress l r) fun parent =>
      (compressMerkleLayer rest).bind fun parents =>
        .pure (parent :: parents)

/-- Build `depth` binary Merkle layers bottom-up from the leaf digest layer,
returning all layers (leaf layer first, root/cap layer last). -/
def buildMerkleLayers {L : ℕ} {Row Salt Digest : Type} :
    ℕ → List Digest → OracleComp (SaltedMerkleAns L Row Salt Digest) (List (List Digest))
  | 0, layer => .pure [layer]
  | depth + 1, layer =>
    (compressMerkleLayer layer).bind fun nextLayer =>
      (buildMerkleLayers depth nextLayer).bind fun rest =>
        .pure (layer :: rest)

theorem noQueryIn_compressMerkleLayer {L : ℕ} {Row Salt Digest : Type}
    (S : Finset (SaltedMerkleQuery L Row Salt Digest))
    (hS : ∀ l r, SaltedMerkleQuery.compress l r ∉ S) :
    ∀ layer : List Digest, NoQueryIn S (compressMerkleLayer layer)
  | [] => trivial
  | [_] => trivial
  | l :: r :: rest =>
    ⟨hS l r, fun _ => noQueryIn_bind (noQueryIn_compressMerkleLayer S hS rest) fun _ => trivial⟩

theorem noQueryIn_buildMerkleLayers {L : ℕ} {Row Salt Digest : Type}
    (S : Finset (SaltedMerkleQuery L Row Salt Digest))
    (hS : ∀ l r, SaltedMerkleQuery.compress l r ∉ S) :
    ∀ (depth : ℕ) (layer : List Digest), NoQueryIn S (buildMerkleLayers depth layer)
  | 0, _ => trivial
  | depth + 1, layer =>
    noQueryIn_bind (noQueryIn_compressMerkleLayer S hS layer) fun nextLayer =>
      noQueryIn_bind (noQueryIn_buildMerkleLayers S hS depth nextLayer) fun _ => trivial

/-- Complete Merkle view exposed to an adversary after opening `opened : Finset (Fin L)`:
the opened rows, opened salts, and the entire list of Merkle layers (which determines the
Merkle commitment/cap, every authentication sibling hash, and every unopened leaf digest). -/
structure SaltedMerkleView (L : ℕ) (Row Salt Digest : Type) (opened : Finset (Fin L)) where
  openedRows : {i : Fin L // i ∈ opened} → Row
  openedSalts : {i : Fin L // i ∈ opened} → Salt
  layers : List (List Digest)

/-- Canonical `Fin`-indexing of `opened` and `unopened = univ \ opened`. -/
noncomputable def openedEquiv {L : ℕ} (opened : Finset (Fin L)) :
    Fin opened.card ≃ {i : Fin L // i ∈ opened} :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe opened)).symm

noncomputable def unopenedEquiv {L : ℕ} (opened : Finset (Fin L)) :
    Fin (Finset.univ \ opened).card ≃ {i : Fin L // i ∈ Finset.univ \ opened} :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe (Finset.univ \ opened))).symm

/-- Reassemble all `L` leaf digests from opened leaf digests and unopened leaf digests. -/
noncomputable def combineLeafDigests {L : ℕ} {Digest : Type} (opened : Finset (Fin L))
    (hOpen : Fin opened.card → Digest)
    (hUnopen : Fin (Finset.univ \ opened).card → Digest) : Fin L → Digest :=
  fun i =>
    if h : i ∈ opened then
      hOpen ((openedEquiv opened).symm ⟨i, h⟩)
    else
      hUnopen ((unopenedEquiv opened).symm ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩⟩)

/-- **Real Salted Merkle Game (for fixed salts):**
hashes all `L` leaves via `RO(.leaf idx row salt)`, builds the Merkle tree via
`RO(.compress ...)`, gives the adversary the opened rows, opened salts, and full
Merkle layers, and runs the adaptive distinguisher `D`. -/
noncomputable def realSaltedMerkleComp {L : ℕ} {Row Salt Digest : Type}
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (saltsOpen : Fin opened.card → Salt)
    (saltsUnopen : Fin (Finset.univ \ opened).card → Salt)
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L Row Salt Digest) Bool) :
    OracleComp (SaltedMerkleAns L Row Salt Digest) Bool :=
  let qOpen : Fin opened.card → SaltedMerkleQuery L Row Salt Digest :=
    fun j => let idx := (openedEquiv opened j).1; .leaf idx (rows idx) (saltsOpen j)
  let qUnopen : Fin (Finset.univ \ opened).card → SaltedMerkleQuery L Row Salt Digest :=
    fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
  (queryFin qOpen).bind fun hOpen =>
    (queryFin qUnopen).bind fun hUnopen =>
      let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
      (buildMerkleLayers depth leaves).bind fun layers =>
        D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩

/-- Real game acceptance probability averaged over uniform independent per-leaf salts. -/
noncomputable def realSaltedMerkleGame {L : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L Row Salt Digest) Bool) : ℝ :=
  (∑ saltsOpen : Fin opened.card → Salt,
    ∑ saltsUnopen : Fin (Finset.univ \ opened).card → Salt,
      prob (fun b _ => b = true)
        (realSaltedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
    ((Fintype.card (Fin opened.card → Salt) : ℝ) *
      (Fintype.card (Fin (Finset.univ \ opened).card → Salt) : ℝ))

/-- **Ideal Salted Merkle Game (Witness-Free Simulator):**
takes ONLY `openedRows : {i // i ∈ opened} → Row` (NO secret unopened rows!).
Queries `RO(.leaf ...)` ONLY on opened leaves, samples **uniformly random independent**
digests `hUnopen` for all unopened leaves without querying `RO`, builds the Merkle tree
via `RO(.compress ...)`, and runs the adaptive distinguisher `D`. -/
noncomputable def idealSaltedMerkleGame {L : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (depth : ℕ) (opened : Finset (Fin L))
    (openedRows : {i : Fin L // i ∈ opened} → Row)
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L Row Salt Digest) Bool) : ℝ :=
  (∑ saltsOpen : Fin opened.card → Salt,
    let qOpen : Fin opened.card → SaltedMerkleQuery L Row Salt Digest :=
      fun j =>
        let idx := openedEquiv opened j
        .leaf idx.1 (openedRows idx) (saltsOpen j)
    expect (fun hOpen lOpen =>
      (∑ hUnopen : Fin (Finset.univ \ opened).card → Digest,
        let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
        prob (fun b _ => b = true)
          ((buildMerkleLayers depth leaves).bind fun layers =>
            D ⟨openedRows, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩) lOpen) /
      (Fintype.card (Fin (Finset.univ \ opened).card → Digest) : ℝ))
      (queryFin qOpen) []) /
    (Fintype.card (Fin opened.card → Salt) : ℝ)

/-- **Unopened Salted Merkle Leaf Hiding Theorem in the ROM (`salted_leaf_rom_indistinguishable`):**
for ANY `L` leaves, ANY secret row vector `rows : Fin L → Row`, ANY opened index subset
`opened : Finset (Fin L)`, and ANY adaptive distinguisher `D` making at most `N_RO` queries
to the random oracle (after viewing the opened rows, opened salts, and the complete Merkle
tree / commitment / sibling hashes), the distinguishing advantage against the witness-free
ideal game (where unopened leaf digests are uniformly random and independent of `rows`) is
bounded strictly by:

  **`|realSaltedMerkleGame - idealSaltedMerkleGame| ≤ N_RO * L_unopened / |Salt|`**. -/
theorem salted_leaf_rom_indistinguishable {L N_RO : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Nonempty Salt] [Fintype Digest] [Nonempty Digest]
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L Row Salt Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |realSaltedMerkleGame depth rows opened D -
      idealSaltedMerkleGame depth opened (fun i => rows i.1) D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (Fintype.card Salt : ℝ) := by
  classical
  set m := (Finset.univ \ opened).card
  have hCardOpenPos : (0 : ℝ) < Fintype.card (Fin opened.card → Salt) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hCardUnopenPos : (0 : ℝ) < Fintype.card (Fin m → Salt) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hCardDigPos : (0 : ℝ) < Fintype.card (Fin m → Digest) :=
    Nat.cast_pos.mpr Fintype.card_pos
  unfold realSaltedMerkleGame idealSaltedMerkleGame
  have hstepOpen : ∀ saltsOpen : Fin opened.card → Salt,
      let qOpen : Fin opened.card → SaltedMerkleQuery L Row Salt Digest :=
        fun j => let idx := openedEquiv opened j; .leaf idx.1 (rows idx.1) (saltsOpen j)
      |(∑ saltsUnopen : Fin m → Salt,
          prob (fun b _ => b = true)
            (realSaltedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
          (Fintype.card (Fin m → Salt) : ℝ) -
        expect (fun hOpen lOpen =>
          (∑ hUnopen : Fin m → Digest,
            let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
            prob (fun b _ => b = true)
              ((buildMerkleLayers depth leaves).bind fun layers =>
                D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
              lOpen) /
          (Fintype.card (Fin m → Digest) : ℝ))
          (queryFin qOpen) []| ≤
      (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
    intro saltsOpen
    dsimp only
    let qOpen : Fin opened.card → SaltedMerkleQuery L Row Salt Digest :=
      fun j => let idx := openedEquiv opened j; .leaf idx.1 (rows idx.1) (saltsOpen j)
    -- Express the Real inner term as an `expect` over `queryFin qOpen`.
    have hRealExp : ∀ saltsUnopen : Fin m → Salt,
        prob (fun b _ => b = true)
          (realSaltedMerkleComp depth rows opened saltsOpen saltsUnopen D) [] =
        expect (fun hOpen lOpen =>
          (∑ hUnopen : Fin m → Digest,
            let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
            let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
              fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
            let lReal := lOpen ++ List.ofFn fun j : Fin m => ⟨qUnopen j, hUnopen j⟩
            prob (fun b _ => b = true)
              ((buildMerkleLayers depth leaves).bind fun layers =>
                D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
              lReal) /
          (Fintype.card (Fin m → Digest) : ℝ))
          (queryFin qOpen) [] := by
      intro saltsUnopen
      unfold realSaltedMerkleComp
      rw [prob_bind]
      refine expect_congr_of_outcome fun hOpen lOpen houtOpen => ?_
      rw [prob_bind]
      let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
        fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
      have hqUnopenInj : Function.Injective qUnopen := by
        intro j₁ j₂ hj
        have hidx : (unopenedEquiv opened j₁).1 = (unopenedEquiv opened j₂).1 := by
          injection hj
        exact (unopenedEquiv opened).injective (Subtype.ext hidx)
      have hlOpenOnlyOpened : ∀ j : Fin m, lOpen.dlookup (qUnopen j) = none := by
        intro j
        refine dlookup_none_of_outcome_queryFin qOpen houtOpen (qUnopen j) ?_ rfl
        intro i heq
        have hidx : (openedEquiv opened i).1 = (unopenedEquiv opened j).1 := by injection heq
        exact (Finset.mem_sdiff.mp (unopenedEquiv opened j).2).2 (hidx ▸ (openedEquiv opened i).2)
      exact expect_queryFin_of_fresh qUnopen hqUnopenInj lOpen hlOpenOnlyOpened _
    simp_rw [hRealExp]
    rw [← expect_sum, ← expect_div_const]
    refine (abs_expect_sub_expect_le _ _ _ _).trans
      (expect_le_of_outcome fun hOpen lOpen houtOpen => ?_)
    have hlOpenFreshAll : ∀ (j : Fin m) (s : Salt),
        lOpen.dlookup (.leaf (unopenedEquiv opened j).1 (rows (unopenedEquiv opened j).1) s) = none := by
      intro j s
      refine dlookup_none_of_outcome_queryFin qOpen houtOpen _ ?_ rfl
      intro i heq
      have hidx : (openedEquiv opened i).1 = (unopenedEquiv opened j).1 := by injection heq
      exact (Finset.mem_sdiff.mp (unopenedEquiv opened j).2).2 (hidx ▸ (openedEquiv opened i).2)
    -- Rewrite Ideal term as a constant average over `saltsUnopen`.
    have hconst :
        (∑ hUnopen : Fin m → Digest,
          let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
          prob (fun b _ => b = true)
            ((buildMerkleLayers depth leaves).bind fun layers =>
              D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
            lOpen) / (Fintype.card (Fin m → Digest) : ℝ) =
        (∑ _saltsUnopen : Fin m → Salt,
          (∑ hUnopen : Fin m → Digest,
            let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
            prob (fun b _ => b = true)
              ((buildMerkleLayers depth leaves).bind fun layers =>
                D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
              lOpen) / (Fintype.card (Fin m → Digest) : ℝ)) /
        (Fintype.card (Fin m → Salt) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hCardUnopenPos.ne']
    conv_lhs => arg 1; arg 2; rw [hconst]
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hCardUnopenPos]
    have hcouple : ∀ (saltsUnopen : Fin m → Salt) (hUnopen : Fin m → Digest),
        let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
        let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
          fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
        let lReal := lOpen ++ List.ofFn fun j : Fin m => ⟨qUnopen j, hUnopen j⟩
        |prob (fun b _ => b = true)
            ((buildMerkleLayers depth leaves).bind fun layers =>
              D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
            lReal -
         prob (fun b _ => b = true)
            ((buildMerkleLayers depth leaves).bind fun layers =>
              D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
            lOpen| ≤
        expect (fun layers lTree =>
          prob (fun _ l' => ∃ j : Fin m, (l'.dlookup (qUnopen j)).isSome)
            (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
            lTree)
          (buildMerkleLayers depth leaves) lOpen := by
      intro saltsUnopen hUnopen
      dsimp only
      let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
        fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
      let S : Finset (SaltedMerkleQuery L Row Salt Digest) := Finset.univ.image qUnopen
      have hNo : NoQueryIn S (buildMerkleLayers depth
          (List.ofFn (combineLeafDigests opened hOpen hUnopen))) := by
        refine noQueryIn_buildMerkleLayers S (fun l r hmem => ?_) _ _
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
        dsimp only [qUnopen] at hj
        cases hj
      have hAgree : LogsAgreeOutside S
          (lOpen ++ List.ofFn fun j : Fin m => ⟨qUnopen j, hUnopen j⟩) lOpen := by
        intro x hx
        rw [List.dlookup_append]
        have hnone : (List.ofFn fun j : Fin m =>
            (⟨qUnopen j, hUnopen j⟩ : Sigma (SaltedMerkleAns L Row Salt Digest))).dlookup x = none := by
          rw [List.dlookup_eq_none]
          intro hmem
          rw [List.keys, List.mem_map] at hmem
          obtain ⟨⟨k, v⟩, hkv, rfl⟩ := hmem
          rw [List.mem_ofFn] at hkv
          obtain ⟨j, hj⟩ := hkv
          exact hx (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, congrArg Sigma.fst hj⟩)
        rw [hnone, Option.or_none]
      have hFresh : LogsFreshOn S lOpen := by
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact hlOpenFreshAll j (saltsUnopen j)
      rw [prob_bind, prob_bind]
      refine abs_expect_sub_expect_le_of_noQueryIn S _ hNo _ _ _ hAgree hFresh ?_
      intro layers l₁' l₂' hA' hF'
      have hhit := abs_prob_sub_prob_le_prob_hit S
        (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩) hA' hF'
      refine hhit.trans (prob_mono (fun _ l' hex => ?_) _ _)
      obtain ⟨x, hxS, hsome⟩ := hex
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxS
      exact ⟨j, hsome⟩
    have htri :
        |∑ saltsUnopen : Fin m → Salt,
          ((∑ hUnopen : Fin m → Digest,
              let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
              let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
                fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
              let lReal := lOpen ++ List.ofFn fun j : Fin m => ⟨qUnopen j, hUnopen j⟩
              prob (fun b _ => b = true)
                ((buildMerkleLayers depth leaves).bind fun layers =>
                  D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                lReal) / (Fintype.card (Fin m → Digest) : ℝ) -
            (∑ hUnopen : Fin m → Digest,
              let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
              prob (fun b _ => b = true)
                ((buildMerkleLayers depth leaves).bind fun layers =>
                  D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                lOpen) / (Fintype.card (Fin m → Digest) : ℝ))| ≤
        ∑ saltsUnopen : Fin m → Salt,
          (∑ hUnopen : Fin m → Digest,
            let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
            let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
              fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
            expect (fun layers lTree =>
              prob (fun _ l' => ∃ j : Fin m, (l'.dlookup (qUnopen j)).isSome)
                (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                lTree)
              (buildMerkleLayers depth leaves) lOpen) / (Fintype.card (Fin m → Digest) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun saltsUnopen _ => ?_)
      rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hCardDigPos]
      refine div_le_div_of_nonneg_right ?_ hCardDigPos.le
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun hUnopen _ => hcouple saltsUnopen hUnopen)
    calc _ ≤ (∑ saltsUnopen : Fin m → Salt,
            (∑ hUnopen : Fin m → Digest,
              let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
              let qUnopen : Fin m → SaltedMerkleQuery L Row Salt Digest :=
                fun j => let idx := (unopenedEquiv opened j).1; .leaf idx (rows idx) (saltsUnopen j)
              expect (fun layers lTree =>
                prob (fun _ l' => ∃ j : Fin m, (l'.dlookup (qUnopen j)).isSome)
                  (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                  lTree)
                (buildMerkleLayers depth leaves) lOpen) / (Fintype.card (Fin m → Digest) : ℝ)) /
            (Fintype.card (Fin m → Salt) : ℝ) :=
          div_le_div_of_nonneg_right htri hCardUnopenPos.le
      _ = (∑ hUnopen : Fin m → Digest,
            let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
            expect (fun layers lTree =>
              (∑ saltsUnopen : Fin m → Salt,
                prob (fun _ l' => ∃ j : Fin m,
                  (l'.dlookup (.leaf (unopenedEquiv opened j).1
                    (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome)
                  (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                  lTree) / (Fintype.card (Fin m → Salt) : ℝ))
              (buildMerkleLayers depth leaves) lOpen) /
          (Fintype.card (Fin m → Digest) : ℝ) := by
          rw [← Finset.sum_div, Finset.sum_comm, div_right_comm, Finset.sum_div]
          congr 1
          refine Finset.sum_congr rfl fun hUnopen _ => ?_
          rw [← expect_sum, ← expect_div_const]
      _ ≤ (∑ _hUnopen : Fin m → Digest, ((N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ))) /
          (Fintype.card (Fin m → Digest) : ℝ) := by
          refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun hUnopen _ => ?_) hCardDigPos.le
          refine expect_le_of_outcome fun layers lTree houtTree => ?_
          have hlTreeFresh : ∀ (j : Fin m) (s : Salt),
              lTree.dlookup (.leaf (unopenedEquiv opened j).1
                (rows (unopenedEquiv opened j).1) s) = none := fun j s =>
            dlookup_none_of_noQueryIn
              (noQueryIn_buildMerkleLayers _ (fun _ _ hm => by
                have h := Finset.mem_singleton.mp hm; cases h) _ _)
              houtTree (hlOpenFreshAll j s)
          exact unifAvg_prob_hit_le
            (fun j s => SaltedMerkleQuery.leaf (unopenedEquiv opened j).1
              (rows (unopenedEquiv opened j).1) s)
            (fun j s₁ s₂ h => by injection h)
            (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
            (hD _) lTree hlTreeFresh
      _ = (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            mul_div_cancel_left₀ _ hCardDigPos.ne']
  have hdiv_rw :
      (∑ saltsOpen : Fin opened.card → Salt,
        ∑ saltsUnopen : Fin m → Salt,
          prob (fun b _ => b = true)
            (realSaltedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
        ((Fintype.card (Fin opened.card → Salt) : ℝ) * (Fintype.card (Fin m → Salt) : ℝ)) =
      (∑ saltsOpen : Fin opened.card → Salt,
        (∑ saltsUnopen : Fin m → Salt,
          prob (fun b _ => b = true)
            (realSaltedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
          (Fintype.card (Fin m → Salt) : ℝ)) /
        (Fintype.card (Fin opened.card → Salt) : ℝ) := by
    rw [← Finset.sum_div, div_div, mul_comm]
  rw [hdiv_rw, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hCardOpenPos]
  calc |∑ saltsOpen : Fin opened.card → Salt, _| / (Fintype.card (Fin opened.card → Salt) : ℝ)
      ≤ (∑ saltsOpen : Fin opened.card → Salt, |_|) /
          (Fintype.card (Fin opened.card → Salt) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hCardOpenPos.le
    _ ≤ (∑ _saltsOpen : Fin opened.card → Salt,
          ((N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ))) /
          (Fintype.card (Fin opened.card → Salt) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hstepOpen s) hCardOpenPos.le
    _ = (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hCardOpenPos.ne']

/-- **Two-Secret Indistinguishability Corollary:**
any two secret row vectors `rows₁, rows₂ : Fin L → Row` that agree on `opened` have
distinguishing advantage at most `2 * N_RO * L_unopened / |Salt|`. -/
theorem salted_leaf_rom_indistinguishable_two_rows {L N_RO : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Nonempty Salt] [Fintype Digest] [Nonempty Digest]
    (depth : ℕ) (rows₁ rows₂ : Fin L → Row) (opened : Finset (Fin L))
    (hAgree : ∀ i ∈ opened, rows₁ i = rows₂ i)
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L Row Salt Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |realSaltedMerkleGame depth rows₁ opened D - realSaltedMerkleGame depth rows₂ opened D| ≤
      2 * ((N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (Fintype.card Salt : ℝ)) := by
  have h1 := salted_leaf_rom_indistinguishable depth rows₁ opened D hD
  have h2 := salted_leaf_rom_indistinguishable depth rows₂ opened D hD
  have hid : (fun i : {i : Fin L // i ∈ opened} => rows₁ i.1) =
      (fun i : {i : Fin L // i ∈ opened} => rows₂ i.1) := by
    funext ⟨i, hi⟩
    exact hAgree i hi
  rw [hid] at h1
  calc |realSaltedMerkleGame depth rows₁ opened D - realSaltedMerkleGame depth rows₂ opened D|
      ≤ |realSaltedMerkleGame depth rows₁ opened D -
          idealSaltedMerkleGame depth opened (fun i => rows₂ i.1) D| +
        |idealSaltedMerkleGame depth opened (fun i => rows₂ i.1) D -
          realSaltedMerkleGame depth rows₂ opened D| := abs_sub_le _ _ _
    _ = |realSaltedMerkleGame depth rows₁ opened D -
          idealSaltedMerkleGame depth opened (fun i => rows₂ i.1) D| +
        |realSaltedMerkleGame depth rows₂ opened D -
          idealSaltedMerkleGame depth opened (fun i => rows₂ i.1) D| := by
        rw [abs_sub_comm (idealSaltedMerkleGame _ _ _ _)]
    _ ≤ _ := by linarith

end SaltedMerkleHiding

/-! ## Section 4: Unindexed `v6-zk` Leaf Hashing (`RO(row || salt)`) -/

section UnindexedSaltedMerkle

/-- Unindexed salted Merkle ROM query type (`RO(row || salt)` without leaf index,
matching `multi-stark/v6-zk`'s `hash_leaf_rows_with_salt`). -/
inductive UnindexedSaltedQuery (Row Salt Digest : Type) where
  | leaf (row : Row) (salt : Salt)
  | compress (left right : Digest)
  deriving DecidableEq

abbrev UnindexedSaltedAns (Row Salt Digest : Type) :
    UnindexedSaltedQuery Row Salt Digest → Type := fun _ => Digest

def compressUnindexedLayer {Row Salt Digest : Type} :
    List Digest → OracleComp (UnindexedSaltedAns Row Salt Digest) (List Digest)
  | [] => .pure []
  | [d] => .pure [d]
  | l :: r :: rest =>
    .queryBind (.compress l r) fun parent =>
      (compressUnindexedLayer rest).bind fun parents =>
        .pure (parent :: parents)

def buildUnindexedMerkleLayers {Row Salt Digest : Type} :
    ℕ → List Digest → OracleComp (UnindexedSaltedAns Row Salt Digest) (List (List Digest))
  | 0, layer => .pure [layer]
  | depth + 1, layer =>
    (compressUnindexedLayer layer).bind fun nextLayer =>
      (buildUnindexedMerkleLayers depth nextLayer).bind fun rest =>
        .pure (layer :: rest)

theorem noQueryIn_compressUnindexedLayer {Row Salt Digest : Type}
    (S : Finset (UnindexedSaltedQuery Row Salt Digest))
    (hS : ∀ l r, UnindexedSaltedQuery.compress l r ∉ S) :
    ∀ layer : List Digest, NoQueryIn S (compressUnindexedLayer layer)
  | [] => trivial
  | [_] => trivial
  | l :: r :: rest =>
    ⟨hS l r, fun _ => noQueryIn_bind (noQueryIn_compressUnindexedLayer S hS rest) fun _ => trivial⟩

theorem noQueryIn_buildUnindexedMerkleLayers {Row Salt Digest : Type}
    (S : Finset (UnindexedSaltedQuery Row Salt Digest))
    (hS : ∀ l r, UnindexedSaltedQuery.compress l r ∉ S) :
    ∀ (depth : ℕ) (layer : List Digest), NoQueryIn S (buildUnindexedMerkleLayers depth layer)
  | 0, _ => trivial
  | depth + 1, layer =>
    noQueryIn_bind (noQueryIn_compressUnindexedLayer S hS layer) fun nextLayer =>
      noQueryIn_bind (noQueryIn_buildUnindexedMerkleLayers S hS depth nextLayer) fun _ => trivial

/-- Real game in the unindexed `RO(row || salt)` model. -/
noncomputable def realUnindexedMerkleComp {L : ℕ} {Row Salt Digest : Type}
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (saltsOpen : Fin opened.card → Salt)
    (saltsUnopen : Fin (Finset.univ \ opened).card → Salt)
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool) :
    OracleComp (UnindexedSaltedAns Row Salt Digest) Bool :=
  let qOpen : Fin opened.card → UnindexedSaltedQuery Row Salt Digest :=
    fun j => .leaf (rows (openedEquiv opened j).1) (saltsOpen j)
  let qUnopen : Fin (Finset.univ \ opened).card → UnindexedSaltedQuery Row Salt Digest :=
    fun j => .leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j)
  (queryFin qOpen).bind fun hOpen =>
    (queryFin qUnopen).bind fun hUnopen =>
      let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
      (buildUnindexedMerkleLayers depth leaves).bind fun layers =>
        D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩

noncomputable def realUnindexedMerkleGame {L : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool) : ℝ :=
  (∑ saltsOpen : Fin opened.card → Salt,
    ∑ saltsUnopen : Fin (Finset.univ \ opened).card → Salt,
      prob (fun b _ => b = true)
        (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
    ((Fintype.card (Fin opened.card → Salt) : ℝ) *
      (Fintype.card (Fin (Finset.univ \ opened).card → Salt) : ℝ))

noncomputable def idealUnindexedMerkleGame {L : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (depth : ℕ) (opened : Finset (Fin L))
    (openedRows : {i : Fin L // i ∈ opened} → Row)
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool) : ℝ :=
  (∑ saltsOpen : Fin opened.card → Salt,
    let qOpen : Fin opened.card → UnindexedSaltedQuery Row Salt Digest :=
      fun j => .leaf (openedRows (openedEquiv opened j)) (saltsOpen j)
    expect (fun hOpen lOpen =>
      (∑ hUnopen : Fin (Finset.univ \ opened).card → Digest,
        let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
        prob (fun b _ => b = true)
          ((buildUnindexedMerkleLayers depth leaves).bind fun layers =>
            D ⟨openedRows, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩) lOpen) /
      (Fintype.card (Fin (Finset.univ \ opened).card → Digest) : ℝ))
      (queryFin qOpen) []) /
    (Fintype.card (Fin opened.card → Salt) : ℝ)

/-- Every unopened leaf's salt is distinct from all other unopened salts and all opened salts. -/
def UnopenedSaltsFresh {k m : ℕ} {Salt : Type}
    (saltsOpen : Fin k → Salt) (saltsUnopen : Fin m → Salt) : Prop :=
  Function.Injective saltsUnopen ∧ ∀ (j : Fin m) (i : Fin k), saltsUnopen j ≠ saltsOpen i

/-- Fraction of `saltsUnopen : Fin m → Salt` violating `UnopenedSaltsFresh saltsOpen`:
at most `m * (k + (m - 1)) / |Salt|`. -/
theorem prob_not_unopenedSaltsFresh_le {k m : ℕ} {Salt : Type} [DecidableEq Salt]
    [Fintype Salt] [Nonempty Salt] (saltsOpen : Fin k → Salt) :
    (∑ saltsUnopen : Fin m → Salt,
        @ite _ (¬ UnopenedSaltsFresh saltsOpen saltsUnopen) (Classical.propDecidable _) (1 : ℝ) 0) /
      (Fintype.card (Fin m → Salt) : ℝ) ≤
      (m : ℝ) * ((k + (m - 1) : ℕ) : ℝ) / (Fintype.card Salt : ℝ) := by
  classical
  have hcard_pos : (0 : ℝ) < Fintype.card (Fin m → Salt) := Nat.cast_pos.mpr Fintype.card_pos
  have hSalt_pos : (0 : ℝ) < Fintype.card Salt := Nat.cast_pos.mpr Fintype.card_pos
  have hpt : ∀ saltsUnopen : Fin m → Salt,
      (@ite _ (¬ UnopenedSaltsFresh saltsOpen saltsUnopen) (Classical.propDecidable _) (1 : ℝ) 0) ≤
        (∑ j : Fin m, ∑ i : Fin k, if saltsUnopen j = saltsOpen i then (1 : ℝ) else 0) +
        (∑ j₁ : Fin m, ∑ j₂ ∈ Finset.univ.erase j₁,
          if saltsUnopen j₁ = saltsUnopen j₂ then (1 : ℝ) else 0) := by
    intro s
    by_cases hgood : UnopenedSaltsFresh saltsOpen s
    · rw [ite_eq_right (not_not.mpr hgood)]
      exact add_nonneg
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
    · rw [ite_eq_left hgood]
      unfold UnopenedSaltsFresh at hgood
      rw [not_and_or] at hgood
      rcases hgood with hnotinj | hhit
      · rw [Function.Injective] at hnotinj
        push Not at hnotinj
        obtain ⟨j₁, j₂, heq, hne⟩ := hnotinj
        have h1 : (1 : ℝ) ≤ ∑ j₂' ∈ Finset.univ.erase j₁,
            if s j₁ = s j₂' then (1 : ℝ) else 0 := by
          have hmem : j₂ ∈ Finset.univ.erase j₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
          have hle := Finset.single_le_sum (f := fun j₂' => if s j₁ = s j₂' then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) hmem
          simpa [heq] using hle
        have h2 : (1 : ℝ) ≤ ∑ j₁' : Fin m, ∑ j₂' ∈ Finset.univ.erase j₁',
            if s j₁' = s j₂' then (1 : ℝ) else 0 :=
          h1.trans (Finset.single_le_sum
            (f := fun j₁' : Fin m => ∑ j₂' ∈ Finset.univ.erase j₁',
              if s j₁' = s j₂' then (1 : ℝ) else 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_univ j₁))
        have hnn : (0 : ℝ) ≤ ∑ j : Fin m, ∑ i : Fin k, if s j = saltsOpen i then 1 else 0 :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
        linarith
      · push Not at hhit
        obtain ⟨j, i, heq⟩ := hhit
        have h1 : (1 : ℝ) ≤ ∑ i' : Fin k, if s j = saltsOpen i' then (1 : ℝ) else 0 := by
          have hle := Finset.single_le_sum (f := fun i' => if s j = saltsOpen i' then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
          simpa [heq] using hle
        have h2 : (1 : ℝ) ≤ ∑ j' : Fin m, ∑ i' : Fin k,
            if s j' = saltsOpen i' then (1 : ℝ) else 0 :=
          h1.trans (Finset.single_le_sum
            (f := fun j' : Fin m => ∑ i' : Fin k, if s j' = saltsOpen i' then (1 : ℝ) else 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_univ j))
        have hnn : (0 : ℝ) ≤ ∑ j₁ : Fin m, ∑ j₂ ∈ Finset.univ.erase j₁,
            if s j₁ = s j₂ then 1 else 0 :=
          Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
        linarith
  have hsingle : ∀ (j : Fin m) (target : Salt),
      (∑ s : Fin m → Salt, if s j = target then (1 : ℝ) else 0) /
        (Fintype.card (Fin m → Salt) : ℝ) = 1 / (Fintype.card Salt : ℝ) := by
    intro j target
    rw [Finset.sum_boole]
    let e : {s : Fin m → Salt // s j = target} ≃ ({j' : Fin m // j' ≠ j} → Salt) :=
      { toFun := fun ⟨f, _⟩ j' => f j'.1
        invFun := fun g => ⟨fun j' => if h : j' = j then target else g ⟨j', h⟩, by simp⟩
        left_inv := fun ⟨f, hf⟩ => by
          apply Subtype.ext; funext j'; dsimp only
          split_ifs with h
          · subst h; exact hf.symm
          · rfl
        right_inv := fun g => by funext ⟨j', hj'⟩; simp [hj'] }
    have hcard : (Finset.univ.filter fun s : Fin m → Salt => s j = target).card =
        (Fintype.card Salt) ^ (m - 1) := by
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    have hm1 : m = (m - 1) + 1 := by have := j.isLt; omega
    rw [hcard, Fintype.card_fun, Fintype.card_fin]
    conv_lhs => arg 2; rw [hm1]
    rw [pow_succ, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow]
    have hp : ((Fintype.card Salt : ℝ) ^ (m - 1)) ≠ 0 := pow_ne_zero _ hSalt_pos.ne'
    field_simp [hp, hSalt_pos.ne']
  have hpair : ∀ (j₁ j₂ : Fin m), j₂ ≠ j₁ →
      (∑ s : Fin m → Salt, if s j₁ = s j₂ then (1 : ℝ) else 0) /
        (Fintype.card (Fin m → Salt) : ℝ) = 1 / (Fintype.card Salt : ℝ) := by
    intro j₁ j₂ hne
    rw [Finset.sum_boole]
    let e : {s : Fin m → Salt // s j₁ = s j₂} ≃ ({j' : Fin m // j' ≠ j₁} → Salt) :=
      { toFun := fun ⟨f, _⟩ j' => f j'.1
        invFun := fun g => ⟨fun j' => if h : j' = j₁ then g ⟨j₂, hne⟩ else g ⟨j', h⟩, by
          simp [hne]⟩
        left_inv := fun ⟨f, hf⟩ => by
          apply Subtype.ext; funext j'; dsimp only
          split_ifs with h
          · subst h; exact hf.symm
          · rfl
        right_inv := fun g => by funext ⟨j', hj'⟩; simp [hj'] }
    have hcard : (Finset.univ.filter fun s : Fin m → Salt => s j₁ = s j₂).card =
        (Fintype.card Salt) ^ (m - 1) := by
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    have hm1 : m = (m - 1) + 1 := by have := j₁.isLt; omega
    rw [hcard, Fintype.card_fun, Fintype.card_fin]
    conv_lhs => arg 2; rw [hm1]
    rw [pow_succ, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow]
    have hp : ((Fintype.card Salt : ℝ) ^ (m - 1)) ≠ 0 := pow_ne_zero _ hSalt_pos.ne'
    field_simp [hp, hSalt_pos.ne']
  calc (∑ s : Fin m → Salt,
          @ite _ (¬ UnopenedSaltsFresh saltsOpen s) (Classical.propDecidable _) (1 : ℝ) 0) /
        (Fintype.card (Fin m → Salt) : ℝ)
      ≤ (∑ s : Fin m → Salt,
          ((∑ j : Fin m, ∑ i : Fin k, if s j = saltsOpen i then (1 : ℝ) else 0) +
           (∑ j₁ : Fin m, ∑ j₂ ∈ Finset.univ.erase j₁,
              if s j₁ = s j₂ then (1 : ℝ) else 0))) /
        (Fintype.card (Fin m → Salt) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hpt s) hcard_pos.le
    _ = (∑ j : Fin m, ∑ i : Fin k,
          (∑ s : Fin m → Salt, if s j = saltsOpen i then (1 : ℝ) else 0) /
            (Fintype.card (Fin m → Salt) : ℝ)) +
        (∑ j₁ : Fin m, ∑ j₂ ∈ Finset.univ.erase j₁,
          (∑ s : Fin m → Salt, if s j₁ = s j₂ then (1 : ℝ) else 0) /
            (Fintype.card (Fin m → Salt) : ℝ)) := by
        rw [Finset.sum_add_distrib, add_div]
        congr 1
        · rw [Finset.sum_comm, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm, Finset.sum_div]
        · rw [Finset.sum_comm, Finset.sum_div]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          rw [Finset.sum_comm, Finset.sum_div]
    _ = (∑ _j : Fin m, ∑ _i : Fin k, (1 / (Fintype.card Salt : ℝ))) +
        (∑ j₁ : Fin m, ∑ _j₂ ∈ Finset.univ.erase j₁, (1 / (Fintype.card Salt : ℝ))) := by
        congr 1
        · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hsingle j _
        · refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ hj₂ =>
            hpair j₁ j₂ (Finset.ne_of_mem_erase hj₂)
    _ = (m : ℝ) * ((k + (m - 1) : ℕ) : ℝ) / (Fintype.card Salt : ℝ) := by
        have herase : ∀ j₁ : Fin m, (Finset.univ.erase j₁).card = m - 1 := fun j₁ => by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j₁), Finset.card_fin]
        simp [herase]
        ring

/-- **Unindexed `v6-zk` Salted Merkle Leaf Hiding (`salted_leaf_unindexed_rom_indistinguishable`):**
in the exact `multi-stark/v6-zk` leaf-hashing model `RO(row || salt)` (without hashing the
leaf index into the leaf), any adaptive `N_RO`-query ROM distinguisher has advantage at most

  **`((N_RO : ℝ) * L_unopened + L_unopened * (L - 1)) / |Salt|`**

against the witness-free ideal game. -/
theorem salted_leaf_unindexed_rom_indistinguishable {L N_RO : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Nonempty Salt] [Fintype Digest] [Nonempty Digest]
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (D : SaltedMerkleView L Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |realUnindexedMerkleGame depth rows opened D -
      idealUnindexedMerkleGame depth opened (fun i => rows i.1) D| ≤
      ((N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) +
        ((Finset.univ \ opened).card : ℝ) * ((L - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ) := by
  classical
  set m := (Finset.univ \ opened).card with hm_def
  have hCardOpenPos : (0 : ℝ) < Fintype.card (Fin opened.card → Salt) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hCardUnopenPos : (0 : ℝ) < Fintype.card (Fin m → Salt) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hCardDigPos : (0 : ℝ) < Fintype.card (Fin m → Digest) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsumL : opened.card + m = L := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ opened)
    simpa [hm_def] using (add_comm _ _).trans h
  have hkm_prod : (m : ℝ) * ((opened.card + (m - 1) : ℕ) : ℝ) ≤ (m : ℝ) * ((L - 1 : ℕ) : ℝ) := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hle : opened.card + (m - 1) ≤ L - 1 := by omega
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (Nat.cast_nonneg m)
  unfold realUnindexedMerkleGame idealUnindexedMerkleGame
  have hstepOpen : ∀ saltsOpen : Fin opened.card → Salt,
      let qOpen : Fin opened.card → UnindexedSaltedQuery Row Salt Digest :=
        fun j => .leaf (rows (openedEquiv opened j).1) (saltsOpen j)
      |(∑ saltsUnopen : Fin m → Salt,
          prob (fun b _ => b = true)
            (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
          (Fintype.card (Fin m → Salt) : ℝ) -
        expect (fun hOpen lOpen =>
          (∑ hUnopen : Fin m → Digest,
            let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
            prob (fun b _ => b = true)
              ((buildUnindexedMerkleLayers depth leaves).bind fun layers =>
                D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
              lOpen) /
          (Fintype.card (Fin m → Digest) : ℝ))
          (queryFin qOpen) []| ≤
      ((N_RO : ℝ) * (m : ℝ) + (m : ℝ) * ((L - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ) := by
    intro saltsOpen
    dsimp only
    let qOpen : Fin opened.card → UnindexedSaltedQuery Row Salt Digest :=
      fun j => .leaf (rows (openedEquiv opened j).1) (saltsOpen j)
    let idealVal : ℝ := expect (fun hOpen lOpen =>
      (∑ hUnopen : Fin m → Digest,
        let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
        prob (fun b _ => b = true)
          ((buildUnindexedMerkleLayers depth leaves).bind fun layers =>
            D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
          lOpen) /
      (Fintype.card (Fin m → Digest) : ℝ)) (queryFin qOpen) []
    change |(∑ saltsUnopen : Fin m → Salt,
        prob (fun b _ => b = true)
          (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
        (Fintype.card (Fin m → Salt) : ℝ) - idealVal| ≤ _
    have hconst : idealVal =
        (∑ _saltsUnopen : Fin m → Salt, idealVal) / (Fintype.card (Fin m → Salt) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hCardUnopenPos.ne']
    have hideal0 : 0 ≤ idealVal :=
      le_expect_of_outcome fun _ _ _ =>
        div_nonneg (Finset.sum_nonneg fun _ _ => prob_nonneg _ _ _) hCardDigPos.le
    have hideal1 : idealVal ≤ 1 := by
      refine expect_le_of_outcome fun _ _ _ => ?_
      rw [div_le_one hCardDigPos]
      calc ∑ _hUnopen : Fin m → Digest, _ ≤ ∑ _hUnopen : Fin m → Digest, (1 : ℝ) :=
            Finset.sum_le_sum fun _ _ => prob_le_one _ _ _
        _ = (Fintype.card (Fin m → Digest) : ℝ) := by simp
    let hitSuffixExp : (Fin m → Salt) → ℝ := fun saltsUnopen =>
      expect (fun hOpen lOpen =>
        (∑ hUnopen : Fin m → Digest,
          let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
          expect (fun layers lTree =>
            prob (fun _ l' => ∃ t, l' = lTree ++ t ∧
              ∃ j : Fin m, (t.dlookup (.leaf (rows (unopenedEquiv opened j).1)
                (saltsUnopen j))).isSome)
              (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
              lTree)
            (buildUnindexedMerkleLayers depth leaves) lOpen) /
        (Fintype.card (Fin m → Digest) : ℝ)) (queryFin qOpen) []
    have hhit_nn : ∀ saltsUnopen, 0 ≤ hitSuffixExp saltsUnopen := fun _ =>
      le_expect_of_outcome fun _ _ _ =>
        div_nonneg (Finset.sum_nonneg fun _ _ =>
          le_expect_of_outcome fun _ _ _ => prob_nonneg _ _ _) hCardDigPos.le
    -- Pointwise bound for every `saltsUnopen`.
    have hper : ∀ saltsUnopen : Fin m → Salt,
        |prob (fun b _ => b = true)
            (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) [] - idealVal| ≤
          hitSuffixExp saltsUnopen +
            (@ite _ (¬ UnopenedSaltsFresh saltsOpen saltsUnopen) (Classical.propDecidable _) (1 : ℝ) 0) := by
      intro saltsUnopen
      by_cases hgood : UnopenedSaltsFresh saltsOpen saltsUnopen
      · rw [ite_eq_right (not_not.mpr hgood), add_zero]
        let qUnopen : Fin m → UnindexedSaltedQuery Row Salt Digest :=
          fun j => .leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j)
        have hqUnopenInj : Function.Injective qUnopen := by
          intro j₁ j₂ hj
          have hs : saltsUnopen j₁ = saltsUnopen j₂ := by injection hj
          exact hgood.1 hs
        have hRealExp :
            prob (fun b _ => b = true)
              (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) [] =
            expect (fun hOpen lOpen =>
              (∑ hUnopen : Fin m → Digest,
                let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
                let lReal := lOpen ++ List.ofFn fun j : Fin m => ⟨qUnopen j, hUnopen j⟩
                prob (fun b _ => b = true)
                  ((buildUnindexedMerkleLayers depth leaves).bind fun layers =>
                    D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                  lReal) / (Fintype.card (Fin m → Digest) : ℝ)) (queryFin qOpen) [] := by
          unfold realUnindexedMerkleComp
          rw [prob_bind]
          refine expect_congr_of_outcome fun hOpen lOpen houtOpen => ?_
          rw [prob_bind]
          have hlOpenFresh : ∀ j : Fin m, lOpen.dlookup (qUnopen j) = none := fun j =>
            dlookup_none_of_outcome_queryFin qOpen houtOpen (qUnopen j)
              (fun i heq => by have hs : saltsOpen i = saltsUnopen j := by injection heq
                               exact hgood.2 j i hs.symm) rfl
          exact expect_queryFin_of_fresh qUnopen hqUnopenInj lOpen hlOpenFresh _
        rw [hRealExp]
        refine (abs_expect_sub_expect_le _ _ _ _).trans
          (expect_mono_of_outcome fun hOpen lOpen houtOpen => ?_)
        rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hCardDigPos]
        refine div_le_div_of_nonneg_right
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun hUnopen _ => ?_))
          hCardDigPos.le
        let S : Finset (UnindexedSaltedQuery Row Salt Digest) := Finset.univ.image qUnopen
        have hNo : NoQueryIn S (buildUnindexedMerkleLayers depth
            (List.ofFn (combineLeafDigests opened hOpen hUnopen))) := by
          refine noQueryIn_buildUnindexedMerkleLayers S (fun l r hmem => ?_) _ _
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
          dsimp only [qUnopen] at hj
          cases hj
        have hAgree : LogsAgreeOutside S
            (lOpen ++ List.ofFn fun j : Fin m => ⟨qUnopen j, hUnopen j⟩) lOpen := by
          intro x hx
          rw [List.dlookup_append]
          have hnone : (List.ofFn fun j : Fin m =>
              (⟨qUnopen j, hUnopen j⟩ : Sigma (UnindexedSaltedAns Row Salt Digest))).dlookup x = none := by
            rw [List.dlookup_eq_none]
            intro hmem
            rw [List.keys, List.mem_map] at hmem
            obtain ⟨⟨k, v⟩, hkv, rfl⟩ := hmem
            rw [List.mem_ofFn] at hkv
            obtain ⟨j, hj⟩ := hkv
            exact hx (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, congrArg Sigma.fst hj⟩)
          rw [hnone, Option.or_none]
        have hFresh : LogsFreshOn S lOpen := by
          intro x hx
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
          exact dlookup_none_of_outcome_queryFin qOpen houtOpen (qUnopen j)
            (fun i heq => by have hs : saltsOpen i = saltsUnopen j := by injection heq
                             exact hgood.2 j i hs.symm) rfl
        rw [prob_bind, prob_bind]
        refine abs_expect_sub_expect_le_of_noQueryIn S _ hNo _ _ _ hAgree hFresh ?_
        intro layers l₁' l₂' hA' hF'
        have hhit := abs_prob_sub_prob_le_prob_hit S
          (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩) hA' hF'
        refine hhit.trans (prob_mono_of_outcome (fun _ l' houtD hex => ?_))
        obtain ⟨t, rfl⟩ := houtD.prefix
        obtain ⟨x, hxS, hsome⟩ := hex
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxS
        have hnone : l₂'.dlookup (qUnopen j) = none := hF' (qUnopen j) hxS
        rw [List.dlookup_append, hnone, Option.none_or] at hsome
        exact ⟨t, rfl, j, hsome⟩
      · rw [ite_eq_left hgood]
        have hr0 := prob_nonneg (fun b _ => b = true)
          (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []
        have hr1 := prob_le_one (fun b _ => b = true)
          (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []
        have habs : |prob (fun b _ => b = true)
            (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) [] - idealVal| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        linarith [hhit_nn saltsUnopen]
    -- Bound average of `hitSuffixExp` over ALL `saltsUnopen` by `N_RO * m / |Salt|`!
    have hhit_avg :
        (∑ saltsUnopen : Fin m → Salt, hitSuffixExp saltsUnopen) /
          (Fintype.card (Fin m → Salt) : ℝ) ≤ (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
      dsimp only [hitSuffixExp]
      rw [← expect_sum, ← expect_div_const]
      refine expect_le_of_outcome fun hOpen lOpen _ => ?_
      rw [← Finset.sum_div, Finset.sum_comm, div_right_comm, Finset.sum_div]
      have hinner_avg : ∀ hUnopen : Fin m → Digest,
          let leaves := List.ofFn (combineLeafDigests opened hOpen hUnopen)
          (∑ saltsUnopen : Fin m → Salt,
            expect (fun layers lTree =>
              prob (fun _ l' => ∃ t, l' = lTree ++ t ∧
                ∃ j : Fin m, (t.dlookup (.leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome)
                (D ⟨fun i => rows i.1, fun i => saltsOpen ((openedEquiv opened).symm i), layers⟩)
                lTree)
              (buildUnindexedMerkleLayers depth leaves) lOpen) / (Fintype.card (Fin m → Salt) : ℝ) ≤
            (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
        intro hUnopen
        dsimp only
        rw [← expect_sum, ← expect_div_const]
        refine expect_le_of_outcome fun layers lTree _ => ?_
        unfold prob
        rw [← expect_sum, ← expect_div_const]
        refine expect_le_of_outcome fun _ l' hout => ?_
        obtain ⟨t, rfl, htlen⟩ := hout.exists_append (hD _)
        have huniq : ∀ t', lTree ++ t = lTree ++ t' → t' = t := fun t' h =>
          (List.append_right_inj lTree).mp h.symm
        have hstep :
            (∑ saltsUnopen : Fin m → Salt,
              @ite _ (∃ t', lTree ++ t = lTree ++ t' ∧
                  ∃ j : Fin m, (t'.dlookup (.leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome)
                (Classical.propDecidable _) (1 : ℝ) 0) ≤
            ∑ j : Fin m, ∑ saltsUnopen : Fin m → Salt,
              if (t.dlookup (.leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome
              then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun saltsUnopen _ => ?_
          by_cases hex : ∃ t', lTree ++ t = lTree ++ t' ∧
              ∃ j : Fin m, (t'.dlookup (.leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome
          · rw [ite_eq_left hex]
            obtain ⟨t', ht', j₀, hj₀⟩ := hex
            rw [huniq t' ht'] at hj₀
            have hle := Finset.single_le_sum
              (f := fun j : Fin m => if (t.dlookup (.leaf (rows (unopenedEquiv opened j).1)
                (saltsUnopen j))).isSome then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ j₀)
            simpa [hj₀] using hle
          · rw [ite_eq_right hex]
            exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
        calc _ ≤ (∑ j : Fin m, ∑ saltsUnopen : Fin m → Salt,
                if (t.dlookup (.leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome
                then (1 : ℝ) else 0) / (Fintype.card (Fin m → Salt) : ℝ) :=
              div_le_div_of_nonneg_right hstep hCardUnopenPos.le
          _ = ∑ j : Fin m, (∑ saltsUnopen : Fin m → Salt,
                if (t.dlookup (.leaf (rows (unopenedEquiv opened j).1) (saltsUnopen j))).isSome
                then (1 : ℝ) else 0) / (Fintype.card (Fin m → Salt) : ℝ) :=
              Finset.sum_div _ _ _
          _ ≤ ∑ _j : Fin m, ((N_RO : ℝ) / (Fintype.card Salt : ℝ)) :=
              Finset.sum_le_sum fun j _ =>
                avg_hit_suffix_single_le
                  (fun j s => UnindexedSaltedQuery.leaf (rows (unopenedEquiv opened j).1) s)
                  (fun _ _ _ h => by injection h) t htlen j
          _ = (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
      calc (∑ hUnopen : Fin m → Digest, _) / (Fintype.card (Fin m → Digest) : ℝ)
          ≤ (∑ _hUnopen : Fin m → Digest, ((N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ))) /
              (Fintype.card (Fin m → Digest) : ℝ) :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum fun h _ => hinner_avg h) hCardDigPos.le
        _ = (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              mul_div_cancel_left₀ _ hCardDigPos.ne']
    conv_lhs => arg 1; arg 2; rw [hconst]
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hCardUnopenPos]
    have hfresh_le :
        (∑ saltsUnopen : Fin m → Salt,
          @ite _ (¬ UnopenedSaltsFresh saltsOpen saltsUnopen) (Classical.propDecidable _) (1 : ℝ) 0) /
        (Fintype.card (Fin m → Salt) : ℝ) ≤
        (m : ℝ) * ((L - 1 : ℕ) : ℝ) / (Fintype.card Salt : ℝ) :=
      (prob_not_unopenedSaltsFresh_le saltsOpen).trans
        (div_le_div_of_nonneg_right hkm_prod (Nat.cast_nonneg _))
    calc |∑ saltsUnopen : Fin m → Salt, _| / (Fintype.card (Fin m → Salt) : ℝ)
        ≤ (∑ saltsUnopen : Fin m → Salt, |_|) / (Fintype.card (Fin m → Salt) : ℝ) :=
          div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hCardUnopenPos.le
      _ ≤ (∑ saltsUnopen : Fin m → Salt,
            (hitSuffixExp saltsUnopen +
              (@ite _ (¬ UnopenedSaltsFresh saltsOpen saltsUnopen) (Classical.propDecidable _) (1 : ℝ) 0))) /
          (Fintype.card (Fin m → Salt) : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hper s) hCardUnopenPos.le
      _ = (∑ saltsUnopen : Fin m → Salt, hitSuffixExp saltsUnopen) /
            (Fintype.card (Fin m → Salt) : ℝ) +
          (∑ saltsUnopen : Fin m → Salt,
            @ite _ (¬ UnopenedSaltsFresh saltsOpen saltsUnopen) (Classical.propDecidable _) (1 : ℝ) 0) /
            (Fintype.card (Fin m → Salt) : ℝ) := by
          rw [Finset.sum_add_distrib, add_div]
      _ ≤ (N_RO : ℝ) * (m : ℝ) / (Fintype.card Salt : ℝ) +
            (m : ℝ) * ((L - 1 : ℕ) : ℝ) / (Fintype.card Salt : ℝ) := add_le_add hhit_avg hfresh_le
      _ = ((N_RO : ℝ) * (m : ℝ) + (m : ℝ) * ((L - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ) := by
          rw [add_div]
  have hdiv_rw :
      (∑ saltsOpen : Fin opened.card → Salt,
        ∑ saltsUnopen : Fin m → Salt,
          prob (fun b _ => b = true)
            (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
        ((Fintype.card (Fin opened.card → Salt) : ℝ) * (Fintype.card (Fin m → Salt) : ℝ)) =
      (∑ saltsOpen : Fin opened.card → Salt,
        (∑ saltsUnopen : Fin m → Salt,
          prob (fun b _ => b = true)
            (realUnindexedMerkleComp depth rows opened saltsOpen saltsUnopen D) []) /
          (Fintype.card (Fin m → Salt) : ℝ)) /
        (Fintype.card (Fin opened.card → Salt) : ℝ) := by
    rw [← Finset.sum_div, div_div, mul_comm]
  rw [hdiv_rw, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hCardOpenPos]
  calc |∑ saltsOpen : Fin opened.card → Salt, _| / (Fintype.card (Fin opened.card → Salt) : ℝ)
      ≤ (∑ saltsOpen : Fin opened.card → Salt, |_|) / (Fintype.card (Fin opened.card → Salt) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hCardOpenPos.le
    _ ≤ (∑ _saltsOpen : Fin opened.card → Salt,
          (((N_RO : ℝ) * (m : ℝ) + (m : ℝ) * ((L - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ))) /
        (Fintype.card (Fin opened.card → Salt) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hstepOpen s) hCardOpenPos.le
    _ = ((N_RO : ℝ) * (m : ℝ) + (m : ℝ) * ((L - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hCardOpenPos.ne']

end UnindexedSaltedMerkle

/-! ## Section 5: Concrete Salt-Size Instantiations (16-Byte 128-Bit vs 32-Byte 256-Bit) -/

section ConcreteSalts

/-- **16-Byte (`s = 128`-bit) Classical Salt Instantiation** (matching `multi-stark/v6-zk`'s
shipped default `ZK_LEAF_SALT_BYTES = 16`):
unopened leaf distinguishing advantage in the classical ROM is at most
`N_RO * L_unopened / 2 ^ 128`. -/
theorem salted_leaf_rom_128bit {L N_RO : ℕ} {Row Digest : Type}
    [DecidableEq Row] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (D : SaltedMerkleView L Row (Fin (2 ^ 128)) Digest opened →
      OracleComp (SaltedMerkleAns L Row (Fin (2 ^ 128)) Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |realSaltedMerkleGame depth rows opened D -
      idealSaltedMerkleGame depth opened (fun i => rows i.1) D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 128 := by
  have h := salted_leaf_rom_indistinguishable depth rows opened D hD
  simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

/-- **32-Byte (`s = 256`-bit) Post-Quantum-Margin Salt Instantiation:**
unopened leaf distinguishing advantage in the classical ROM is at most
`N_RO * L_unopened / 2 ^ 256`. -/
theorem salted_leaf_rom_256bit {L N_RO : ℕ} {Row Digest : Type}
    [DecidableEq Row] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
    (D : SaltedMerkleView L Row (Fin (2 ^ 256)) Digest opened →
      OracleComp (SaltedMerkleAns L Row (Fin (2 ^ 256)) Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |realSaltedMerkleGame depth rows opened D -
      idealSaltedMerkleGame depth opened (fun i => rows i.1) D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 256 := by
  have h := salted_leaf_rom_indistinguishable depth rows opened D hD
  simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Concrete numerical corollary for 16-byte (`128`-bit) salts: for any Merkle tree with
`L_unopened ≤ 2 ^ 32` unopened leaves (covering all Goldilocks two-adic LDE heights `≤ 2 ^ 32`),
classical distinguishing advantage is at most `N_RO / 2 ^ 96`. -/
theorem salt128_advantage_le_of_leaves_le_pow32 {N_RO L_unopened : ℕ} (hL : L_unopened ≤ 2 ^ 32) :
    (N_RO : ℝ) * (L_unopened : ℝ) / (2 : ℝ) ^ 128 ≤ (N_RO : ℝ) / (2 : ℝ) ^ 96 := by
  have hLr : (L_unopened : ℝ) ≤ (2 : ℝ) ^ 32 := by exact_mod_cast hL
  have h128 : (2 : ℝ) ^ 128 = (2 : ℝ) ^ 32 * (2 : ℝ) ^ 96 := by rw [← pow_add]
  rw [h128]
  have hpos32 : (0 : ℝ) < (2 : ℝ) ^ 32 := by positivity
  have hpos96 : (0 : ℝ) < (2 : ℝ) ^ 96 := by positivity
  calc (N_RO : ℝ) * (L_unopened : ℝ) / ((2 : ℝ) ^ 32 * (2 : ℝ) ^ 96)
      ≤ (N_RO : ℝ) * (2 : ℝ) ^ 32 / ((2 : ℝ) ^ 32 * (2 : ℝ) ^ 96) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLr (Nat.cast_nonneg _))
          (mul_pos hpos32 hpos96).le
    _ = (N_RO : ℝ) / (2 : ℝ) ^ 96 := by field_simp [hpos32.ne', hpos96.ne']

/-- Concrete numerical corollary for 32-byte (`256`-bit) salts: for any Merkle tree with
`L_unopened ≤ 2 ^ 32` unopened leaves and any classical adversary making `N_RO ≤ 2 ^ 128`
queries, the distinguishing advantage is at most `1 / 2 ^ 96` (full `128`-bit classical margin
even with `2 ^ 32` leaves: `N_RO * L_unopened / 2 ^ 256 ≤ N_RO / 2 ^ 224 ≤ 1 / 2 ^ 96`). -/
theorem salt256_advantage_le_of_leaves_le_pow32 {N_RO L_unopened : ℕ}
    (hL : L_unopened ≤ 2 ^ 32) (hN : N_RO ≤ 2 ^ 128) :
    (N_RO : ℝ) * (L_unopened : ℝ) / (2 : ℝ) ^ 256 ≤ 1 / (2 : ℝ) ^ 96 := by
  have hLr : (L_unopened : ℝ) ≤ (2 : ℝ) ^ 32 := by exact_mod_cast hL
  have hNr : (N_RO : ℝ) ≤ (2 : ℝ) ^ 128 := by exact_mod_cast hN
  have h256 : (2 : ℝ) ^ 256 = (2 : ℝ) ^ 128 * (2 : ℝ) ^ 32 * (2 : ℝ) ^ 96 := by
    rw [← pow_add, ← pow_add]
  rw [h256]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 128 * (2 : ℝ) ^ 32 := by positivity
  have hpos96 : (0 : ℝ) < (2 : ℝ) ^ 96 := by positivity
  calc (N_RO : ℝ) * (L_unopened : ℝ) / ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 32 * (2 : ℝ) ^ 96)
      ≤ (2 : ℝ) ^ 128 * (2 : ℝ) ^ 32 / ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 32 * (2 : ℝ) ^ 96) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hNr hLr (Nat.cast_nonneg _) (by positivity))
          (mul_pos hpos hpos96).le
    _ = 1 / (2 : ℝ) ^ 96 := by field_simp [hpos.ne', hpos96.ne']

/-- Pure cardinality-ratio tradeoff illustrating the post-quantum Grover preimage margin
between 16-byte (`128`-bit) and 32-byte (`256`-bit) leaf salts:
* For `128`-bit salt, the generic Grover multi-target search ratio `Q ^ 2 * L / 2 ^ 128`
  reaches `1` already at `Q = 2 ^ 64` (even for `L = 1`).
* For `256`-bit salt, `Q ^ 2 * L / 2 ^ 256 ≤ 1 / 2 ^ 32` even at `Q = 2 ^ 96` and
  `L = 2 ^ 32` (and `≤ 1` up to `Q = 2 ^ 112`, `L = 2 ^ 32`).
*(Arithmetic cardinality ratio only; formal ROM proofs in this module are classical.)* -/
theorem salt128_vs_salt256_grover_ratio_tradeoff :
    (1 : ℝ) ≤ ((2 ^ 64 : ℕ) : ℝ) ^ 2 * 1 / (2 : ℝ) ^ 128 ∧
    ((2 ^ 96 : ℕ) : ℝ) ^ 2 * ((2 ^ 32 : ℕ) : ℝ) / (2 : ℝ) ^ 256 ≤ 1 / (2 : ℝ) ^ 32 := by
  constructor <;> norm_num

end ConcreteSalts

end CertiFri.Zk
