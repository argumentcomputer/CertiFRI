import CertiFriProofs.Theory.Oracle.MerkleFrozen

/-!
# The rows a Merkle root commits to

The reading of a Merkle root against a log: `committedRow l root dims m i` is a
row that some opening in `l` under `root` shows as row `i` of matrix `m`, or
`none` if no opening shows one. The row is chosen classically; in a log without
a collision there is at most one.

## Results

* `committedRow_of_opens`: in a log without a collision, an opening in the log
  shows the committed rows.
* `showsRow_of_committedRow`: a committed row is shown by an opening in the log.
* `committedRow_append_of_not_hit`, `committedRow_concat_of_not_hit`: if `root`
  is present in `l` and no new entry is a hit (`Hit`), the committed rows of
  `root` do not change. No assumption is made on `l`: it may have collisions.
* `committedRow_append_chal`: a new challenge entry changes no committed row.
* `settles_of_committedRow`: the last two facts, as the hypothesis `Settles` of
  the Fiat–Shamir theorem for interpreted messages
  (`prob_fsExperiment_bind_interp_le`), with the bad event `Hit`. It holds for
  every reading of a prover message that looks only at the committed rows of
  the digests the message contains.
* `prob_fsExperiment_bind_committedRow_le`: that theorem with the probability
  of a hit added: an event of the verifier that implies "the transcript, read
  from the committed rows of the final log, is not doomed" has probability at
  most `N * εmax + (K * r + 3) * N * (N - 1) / (2 * card D)` for `N` queries in
  all.

Not covered: the reading of a root as a function on a domain, or as a codeword.
That is built from `committedRow` where the protocol is fixed.
-/

namespace CertiFri.Oracle

universe u u₂ w w'

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

open OracleComp Merkle

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))]

/-- Some opening in the log `l` under `root` shows `row` as the row `i` of
matrix `m`: it is at an index that addresses that row, and its row for matrix
`m` is `row`. -/
def ShowsRow (l : Log (MerkleAnswer Msg Chal T D)) (root : D) (dims : Array Dimensions)
    (m i : ℕ) (row : Array T) : Prop :=
  ∃ index rows d, Opens l root dims index rows ∧ dims[m]? = some d
    ∧ index >>> (maxLogHeight dims.toList - d.logHeight) = i ∧ rows[m]? = some row

open Classical in
/-- The row `i` of matrix `m` that `root` commits to, read against the log `l`:
a row that some opening in `l` shows there, or `none` if there is none. -/
noncomputable def committedRow (l : Log (MerkleAnswer Msg Chal T D)) (root : D)
    (dims : Array Dimensions) (m i : ℕ) : Option (Array T) :=
  if h : ∃ row, ShowsRow l root dims m i row then some (Classical.choose h) else none

section Row

variable {l l' : Log (MerkleAnswer Msg Chal T D)} {root : D} {dims : Array Dimensions}
  {m i : ℕ}

/-- A committed row is shown by an opening in the log. -/
theorem showsRow_of_committedRow {row : Array T} (h : committedRow l root dims m i = some row) :
    ShowsRow l root dims m i row := by
  unfold committedRow at h
  split at h
  · next hex =>
    obtain rfl := Option.some.inj h
    exact Classical.choose_spec hex
  · cases h

/-- No row is committed exactly when no opening in the log shows one. -/
theorem committedRow_eq_none_iff :
    committedRow l root dims m i = none ↔ ∀ row, ¬ ShowsRow l root dims m i row := by
  unfold committedRow
  split
  · next hex => simpa using hex
  · next hex => simpa using hex

/-- An opening has a row for each matrix, and shows it. -/
theorem Opens.showsRow {index : ℕ} {rows : Array (Array T)} {d : Dimensions}
    (h : Opens l root dims index rows) (hd : dims[m]? = some d) :
    ∃ row, rows[m]? = some row
      ∧ ShowsRow l root dims m (index >>> (maxLogHeight dims.toList - d.logHeight)) row := by
  have hm : m < rows.size := by
    rw [h.size_rows]
    exact (Array.getElem?_eq_some_iff.mp hd).1
  exact ⟨rows[m], Array.getElem?_eq_getElem hm, index, rows, d, h, hd, rfl,
    Array.getElem?_eq_getElem hm⟩

/-- **An opening shows the committed row.** In a log without a collision, an
opening in the log shows, for each matrix, the row the root commits to at the
row the index addresses. -/
theorem committedRow_of_opens {index : ℕ} {rows : Array (Array T)} {d : Dimensions}
    (hl : ¬ LogCollision hashObs l) (h : Opens l root dims index rows)
    (hd : dims[m]? = some d) :
    committedRow l root dims m (index >>> (maxLogHeight dims.toList - d.logHeight))
      = rows[m]? := by
  obtain ⟨row, hrow, hshows⟩ := h.showsRow hd
  have hex : ∃ row,
      ShowsRow l root dims m (index >>> (maxLogHeight dims.toList - d.logHeight)) row :=
    ⟨row, hshows⟩
  obtain ⟨index', rows', d', h', hd', hindex', hrow'⟩ := Classical.choose_spec hex
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  rw [committedRow, dite_eq_left hex, ← hrow']
  exact h'.row_eq hl h hd hindex'

/-- The committed rows only depend on the openings the log holds. -/
theorem committedRow_congr
    (h : ∀ index rows, Opens l root dims index rows ↔ Opens l' root dims index rows) :
    committedRow l root dims = committedRow l' root dims := by
  have hopens : Opens l root dims = Opens l' root dims :=
    funext fun index => funext fun rows => propext (h index rows)
  funext m i
  unfold committedRow ShowsRow
  rw [hopens]

/-- **A new challenge entry changes no committed row.** -/
theorem committedRow_append_chal (l : Log (MerkleAnswer Msg Chal T D)) {j : ℕ}
    (t : Transcript Msg Chal j) (msg : Msg) (c : Chal j) (root : D) (dims : Array Dimensions) :
    committedRow (l ++ [⟨.chal t msg, c⟩]) root dims = committedRow l root dims :=
  committedRow_congr fun _ _ => opens_append_chal t msg c

variable {digestsOf : ℕ → Msg → List D} {r : ℕ}

/-- **The committed rows of a present root are frozen.** If `root` is present
in the log `l`, and no entry of `l ++ t` after `l` is a hit with respect to the
entries before it, then `root` commits to the same rows in `l ++ t` as in `l`. -/
theorem committedRow_append_of_not_hit {t : Log (MerkleAnswer Msg Chal T D)}
    (hroot : Present digestsOf r l root)
    (hno : ¬ HasBadFrom (Hit digestsOf r) l.length (l ++ t)) (dims : Array Dimensions) :
    committedRow (l ++ t) root dims = committedRow l root dims :=
  committedRow_congr fun _ _ => opens_append_iff_of_not_hit hroot hno

/-- If `root` is present in the log `l` and the new entry `e` is not a hit, then
`root` commits to the same rows in `l ++ [e]` as in `l`. -/
theorem committedRow_concat_of_not_hit {e : Sigma (MerkleAnswer Msg Chal T D)}
    (hroot : Present digestsOf r l root) (he : ¬ Hit digestsOf r l e.1 e.2)
    (dims : Array Dimensions) :
    committedRow (l ++ [e]) root dims = committedRow l root dims :=
  committedRow_congr fun _ _ => opens_concat_iff_of_not_hit hroot he

end Row

/-- **Readings built from committed rows are settled.** Let `read j m c` read
the prover message `m` of round `j` from the committed rows `c`, such that in a
round below `r` it only looks at the rows of the digests `digestsOf j m`, and
from round `r` on it does not look at `c`. Then the interpretation that reads
every message from the committed rows of the log is settled by the challenge
queries, up to the bad event `Hit`. -/
theorem settles_of_committedRow {Msg₂ : Type u₂} (digestsOf : ℕ → Msg → List D) (r : ℕ)
    (read : ℕ → Msg → (D → Array Dimensions → ℕ → ℕ → Option (Array T)) → Msg₂)
    (hread : ∀ j m c c', j < r → (∀ root ∈ digestsOf j m, c root = c' root) →
      read j m c = read j m c')
    (hconst : ∀ j m c c', r ≤ j → read j m c = read j m c') :
    Settles (fun (l : Log (MerkleAnswer Msg Chal T D)) j m => read j m (committedRow l))
      (Hit digestsOf r) where
  chal l _ t m c j m' :=
    congrArg (read j m') (funext fun root => funext fun dims =>
      committedRow_append_chal l t m c root dims)
  stable l e j m hm he := by
    rcases Nat.lt_or_ge j r with hj | hj
    · exact hread j m _ _ hj fun root hroot => funext fun dims =>
        committedRow_concat_of_not_hit (present_of_mentions hm hj hroot) he dims
    · exact hconst j m _ _ hj

/-! ## Fiat–Shamir for messages read from committed rows -/

section Bound

variable [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)] [Fintype D] [Nonempty D]
  {Msg₂ : Type u₂} {α : Type w} {β : Type w'} {r : ℕ}
  {doomed : ∀ i, Transcript Msg₂ Chal i → Prop} {ε : ℕ → ℝ} {εmax : ℝ}

/-- **Fiat–Shamir when the messages are Merkle roots.** The state function
`doomed` of the underlying protocol is round-by-round sound for `r` rounds with
every error at most `εmax`, and the empty transcript is doomed. Every challenge
query contains at most `M` digests across rounds `< r` (under round-indexed
`digestsOf`), and `read j m c` reads the message `m` of round `j` from the
committed rows `c` of the digests in `digestsOf j m`. An adversary makes at most
`Q` queries and outputs prover messages, the verifier derives the challenges and
then runs `rest`, with at most `R` queries. Suppose that after an outcome of the
experiment, the event `E` of `rest` in a log without a hit implies that the
transcript, read from the committed rows of that log, is not doomed. Then `E`
happens with probability at most
`N * εmax + (max M 3 + 3) * N ^ 2 / (4 * card D)`, where `N = Q + r + R`. -/
theorem prob_fsExperiment_bind_committedRow_le (hsound : RbrSound r doomed ε)
    (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {digestsOf : ℕ → Msg → List D} {M : ℕ}
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    {read : ℕ → Msg → (D → Array Dimensions → ℕ → ℕ → Option (Array T)) → Msg₂}
    (hread : ∀ j m c c', (∀ root ∈ digestsOf j m, c root = c' root) → read j m c = read j m c')
    {adv : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r → OracleComp (MerkleAnswer Msg Chal T D) β} {R : ℕ}
    (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (MerkleAnswer Msg Chal T D) → Prop}
    (hE : ∀ (out : α × Transcript Msg Chal r) (l : Log (MerkleAnswer Msg Chal T D)) (b : β)
      (l' : Log (MerkleAnswer Msg Chal T D)), Outcome (fsExperiment r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' → ¬ HasBad (Hit digestsOf r) l' →
      ¬ doomed r (out.2.mapIdx fun j m => read j m (committedRow l'))) :
    prob E ((fsExperiment r adv msgs).bind rest) []
      ≤ (Q + r + R) * εmax
        + ((max M 3 + 3 : ℕ) : ℝ) * ((Q : ℝ) + r + R) ^ 2 / (4 * Fintype.card D) := by
  -- From round `r` on, a message is read without the log.
  have hset := settles_of_committedRow (Chal := Chal) digestsOf r
    (fun j m c => read j m (if j < r then c else fun _ _ _ _ => none))
    (fun j m c c' hj hc => by simp only [hj, ↓reduceIte]; exact hread j m c c' hc)
    (fun j m c c' hj => by simp only [Nat.not_lt.mpr hj, ↓reduceIte])
  have hflip := prob_fsExperiment_bind_interp_le hsound hε h0 hnil hset hadv msgs hrest
    (E := E) fun out l b l' hout hrun hb hno => by
      -- The transcript has `r` rounds, so each of its messages is read from the log.
      rw [Transcript.mapIdx_congr out.2 (g := fun j m => read j m (committedRow l'))
        fun j m hj => by
          have hjr : j < r := out.2.length_msgs ▸ (List.getElem?_eq_some_iff.mp hj).1
          simp only [hjr, ↓reduceIte]]
      exact hE out l b l' hout hrun hb hno
  have hhit := prob_hasBad_hit_le (r := r) hM
    ((queryBound_fsExperiment (r := r) hadv msgs).bind hrest)
  rw [show ((Q + r + R : ℕ) : ℝ) = (Q : ℝ) + r + R by push_cast; rfl] at hhit
  exact (prob_le_prob_and_not_add E (fun _ l => HasBad (Hit digestsOf r) l) _ _).trans
    (add_le_add hflip hhit)

end Bound

end CertiFri.Oracle
