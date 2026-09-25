import Twentyfifth.Record

/-!
# The twenty-third mapped in, the map back, and what forgetting the filled triples loses

**The twenty-third maps one to one.**  Its states read as states with nothing
filled (`embed`): two of its results are one result here exactly when they are
one result there (`embed_same_iff`); each of its changes is carried to the same
change here (`embed_step`, `embed_reach`); its cost is the cost here
(`cost25_embed_iff`).  So no two twenty-third results are made one here, and a
merge loses nothing.

**The other seeds of the line do not map one to one**: they already did not
into the twenty-third (23:D9), and the embedding keeps the merges — the
seventh's pair `a b; arb arb`, `a b; arb bra` (also two twenty-second
results and two ninth states) and the first's pair `a b c; arb arc`,
`a b c; bra cra` are one result here (`seventh_pair_merge25`,
`first_pair_merge25`).

**Forgetting the filled triples** is a map from this seed's results to the
twenty-third's (`forget_same`); it is not one to one: `a b c` with `a b c`
filled and `a b c` with nothing filled are two results here and one there
(`forget_loses`) — what it loses is the filled triples and their record.

**The map back** (`readBack25`): the twenty-third result of a result with
nothing filled, "none" otherwise.  It depends on the result only
(`readBack25_congr`) and returns the original on every mapped result
(`readBack25_embed`); every result it answers "none" on costs at least four
(`readBack25_none_cost`), and the ones costing four are `a b c` with one
triple filled and nothing asserted (`readBack25_none_smallest`) — one result
in every writing (`Rename.lean`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- **Two twenty-third results are one result here exactly when they are one there.** -/
theorem embed_same_iff {G H : St} : Same25 (embed G) (embed H) ↔ Same3 G H :=
  ⟨fun s => s.1, fun s => ⟨s, List.Perm.refl _⟩⟩

/-- The seventh's pair, two seventh results in every writing (23:D9), is one result here. -/
theorem seventh_pair_merge25 : Same25 (embed (ofR arbTwice)) (embed (ofR arbBra)) :=
  embed_same_iff.2 seventh_pair_merge

/-- The first seed's pair, different in every writing (23:D9), is one result here. -/
theorem first_pair_merge25 : Same25 (embed (ofR outStar)) (embed (ofR inStar)) :=
  embed_same_iff.2 first_pair_merge

/-- Forgetting the filled triples carries this seed's sameness to the twenty-third's. -/
theorem forget_same {A B : FSt} (h : Same25 A B) : Same3 A.G B.G := h.1

/-- **Forgetting the filled triples is not one to one**: `a b c` filled at `a b c`, and `a b c` with nothing
filled, are two results here and one twenty-third result. -/
theorem forget_loses : Same3 oneFilled.G (embed ⟨3, []⟩).G ∧ ¬ Same25 oneFilled (embed ⟨3, []⟩) := by
  refine ⟨Same3.refl _, fun s => ?_⟩
  have := s.2.length_eq
  simp [oneFilled, embed] at this

/-- The map back: the twenty-third result of a result with nothing filled; "none" otherwise. -/
def readBack25 (A : FSt) : Option St :=
  match A.F with
  | [] => some A.G
  | _ :: _ => none

/-- **On every mapped result the map back returns the original.** -/
theorem readBack25_embed (G : St) : readBack25 (embed G) = some G := rfl

theorem readBack25_none_iff (A : FSt) : readBack25 A = none ↔ A.F ≠ [] := by
  unfold readBack25
  cases A.F with
  | nil => simp
  | cons t l => simp

theorem readBack25_some {A : FSt} {G : St} (h : readBack25 A = some G) : A = embed G := by
  unfold readBack25 at h
  cases A with
  | mk G' F =>
    cases F with
    | nil =>
      simp only [Option.some.injEq] at h
      subst h
      rfl
    | cons t l => simp at h

/-- The map back depends on the result only. -/
theorem readBack25_congr {A B : FSt} (s : Same25 A B) :
    (readBack25 A = none ↔ readBack25 B = none) ∧
      ∀ G H, readBack25 A = some G → readBack25 B = some H → Same3 G H := by
  refine ⟨?_, fun G H hA hB => ?_⟩
  · rw [readBack25_none_iff, readBack25_none_iff]
    constructor
    · intro h e
      exact h (perm_nil_eq (e ▸ s.2))
    · intro h e
      exact h (perm_nil_eq (e ▸ s.2.symm))
  · have a := readBack25_some hA
    have b := readBack25_some hB
    subst a
    subst b
    exact s.1

theorem readBack25_oneFilled : readBack25 oneFilled = none := rfl

/-- A well-formed state with something filled has at least three terms. -/
theorem three_le_of_filled {A : FSt} (hw : A.WF) {t : Tri} (ht : t ∈ A.F) : 3 ≤ A.G.n := by
  obtain ⟨⟨a, b, c⟩, ⟨d1, d2, d3⟩, _⟩ := hw.2.1 t ht
  omega

/-- **Every result the map back answers "none" on costs at least four changes.** -/
theorem readBack25_none_cost {A : FSt} (h : readBack25 A = none) {c : Nat} (hc : Cost25 A c) :
    4 ≤ c := by
  obtain ⟨⟨B, s, r⟩, _⟩ := hc
  have hB := r.wf empty25_wf
  have hF : B.F ≠ [] := by
    intro e
    exact (readBack25_none_iff A).1 h (perm_nil_eq (e ▸ s.2.symm))
  obtain ⟨t, ht⟩ : ∃ t, t ∈ B.F := by
    cases e : B.F with
    | nil => exact absurd e hF
    | cons t l => exact ⟨t, List.mem_cons_self⟩
  have h3 := three_le_of_filled hB ht
  have hl : 1 ≤ B.F.length := length_pos_of_mem' ht
  have b := r.psi_le
  rw [psi_empty25] at b
  simp only [psi, phi] at b
  omega

/-- A triple written from its least term, three different terms below three: `0 1 2` or `0 2 1`. -/
theorem tri_three {t : Tri} (hw : t.Within 3) (hd : t.Distinct) (hn : t.norm = t) :
    t = ⟨0, 1, 2⟩ ∨ t = ⟨0, 2, 1⟩ := by
  obtain ⟨x, y, z⟩ := t
  have hx : x < 3 := hw.1
  have hy : y < 3 := hw.2.1
  have hz : z < 3 := hw.2.2
  have d1 : x ≠ y := hd.1
  have d2 : y ≠ z := hd.2.1
  have d3 : x ≠ z := hd.2.2
  have l := Tri.norm_least ⟨x, y, z⟩
  rw [hn] at l
  have l1 : x ≤ y := l.1
  have l2 : x ≤ z := l.2
  have ex : x = 0 := by omega
  subst ex
  rcases lt_three hy with rfl | rfl | rfl <;> rcases lt_three hz with rfl | rfl | rfl <;>
    first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; omega)

/-- **The results the map back answers "none" on at cost four are `a b c` with one triple filled and nothing
asserted**, either way round — one result in every writing (`oneFilled_sameW_other`). -/
theorem readBack25_none_smallest {A : FSt} (h : readBack25 A = none) (hc : Cost25 A 4) :
    Same25 A oneFilled ∨ Same25 A oneFilledOther := by
  obtain ⟨⟨B, s, r⟩, _⟩ := hc
  have hB := r.wf empty25_wf
  have hF : B.F ≠ [] := by
    intro e
    exact (readBack25_none_iff A).1 h (perm_nil_eq (e ▸ s.2.symm))
  obtain ⟨t, l, hBF⟩ : ∃ t l, B.F = t :: l := by
    cases e : B.F with
    | nil => exact absurd e hF
    | cons t l => exact ⟨t, l, rfl⟩
  have ht : t ∈ B.F := by rw [hBF]; exact List.mem_cons_self
  have h3 := three_le_of_filled hB ht
  have b := r.psi_le
  rw [psi_empty25] at b
  simp only [psi, phi, hBF, List.length_cons] at b
  have hn : B.G.n = 3 := by omega
  have hl : l = [] := by
    cases l with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons] at b; omega
  have hp : (plain B.G.A).length = 0 := by omega
  have hp' : plain B.G.A = [] := by
    cases e : plain B.G.A with
    | nil => rfl
    | cons _ _ => rw [e] at hp; simp at hp
  have z0 : Same B.G ⟨3, []⟩ :=
    same_iff_excess.2 ⟨hn, fun x y => (excess_zero_of_plain_nil hp' x y).trans (excess_nothing 3 x y).symm⟩
  have z : Same3 B.G ⟨3, []⟩ := Same.same3 z0
  obtain ⟨hw3, hd, hnorm⟩ := hB.2.1 t ht
  rw [hn] at hw3
  subst hl
  rcases tri_three hw3 hd hnorm with e | e
  · left
    exact s.symm.trans ⟨z, by rw [hBF, e]; exact List.Perm.refl _⟩
  · right
    exact s.symm.trans ⟨z, by rw [hBF, e]; exact List.Perm.refl _⟩

end Twentyfifth
