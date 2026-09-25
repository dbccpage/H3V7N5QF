import Twentythird.Reach

/-!
# Rewriting the terms: the full sameness

"Two results that differ only in how their terms are written, only by an
`xry` and an `xsy` asserted together, or only by raising terms, are the same
result."  A rewriting of the terms `0 … n − 1` is a one-to-one `f` with an
inverse `g` on them (the twenty-second's `IsRw`).  `SameW3 G H`: some
rewriting of `G` is `H` up to this seed's sameness at a fixed writing.

Derived here:
* a rewriting carries the excess along (`excess_rename`), so `Same3` is
  carried along (`Same3.rename`);
* `SameW3` is an equivalence (`SameW3.refl`, `SameW3.symm`, `SameW3.trans`)
  and is exactly the equivalence the seed's three clauses and rewriting
  generate (`genW3_iff_sameW3`);
* the fewest changes to a result, writing included, is its cost
  (`cost3_every_writing`);
* the result asserting nothing is the same in every writing
  (`sameW3_nothing_iff`).
-/

namespace Twentythird

open Twentysecond

theorem count_mapT_injOn {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) (q : Rel) {x y : Nat} (hx : x < n)
    (hy : y < n) :
    ∀ l : List Atom, (∀ a ∈ l, a.x < n ∧ a.y < n) → (l.map (Atom.mapT f)).count ⟨q, f x, f y⟩ = l.count ⟨q, x, y⟩
  | [], _ => rfl
  | a :: t, hl => by
    rw [List.map_cons, count_cons', count_cons',
      count_mapT_injOn h q hx hy t (fun b hb => hl b (List.mem_cons_of_mem _ hb))]
    have ha := hl a List.mem_cons_self
    by_cases e : a = ⟨q, x, y⟩
    · subst e
      rw [if_pos (show (⟨q, x, y⟩ : Atom).mapT f = ⟨q, f x, f y⟩ from rfl),
        if_pos (rfl : (⟨q, x, y⟩ : Atom) = ⟨q, x, y⟩)]
    · have e' : ¬ a.mapT f = ⟨q, f x, f y⟩ := fun h' => e (mapT_inj h ha ⟨hx, hy⟩ h')
      rw [if_neg e, if_neg e']

/-- **A rewriting carries the excess along.** -/
theorem excess_rename {G : St} {f g : Nat → Nat} (h : IsRw G.n f g) (hw : G.WF) {x y : Nat} (hx : x < G.n)
    (hy : y < G.n) : excess (G.rename f) (f x) (f y) = excess G x y := by
  unfold excess
  simp only [St.rename]
  rw [count_mapT_injOn h .r hx hy G.A hw, count_mapT_injOn h .s hx hy G.A hw]

theorem Same3.rename {G H : St} {f g : Nat → Nat} (s : Same3 G H) (h : IsRw G.n f g) (hG : G.WF) (hH : H.WF) :
    Same3 (G.rename f) (H.rename f) := by
  obtain ⟨hn, w, hw⟩ := s
  have hH' : IsRw H.n f g := hn ▸ h
  refine ⟨hn, fun u => w (g u), fun u v hu hv => ?_⟩
  show excess (G.rename f) u v = excess (H.rename f) u v + (w (g u) - w (g v))
  have hu' : u < G.n := hu
  have hv' : v < G.n := hv
  have e1 := excess_rename h hG (h.g_lt u hu') (h.g_lt v hv')
  have e2 := excess_rename hH' hH (hn ▸ h.g_lt u hu') (hn ▸ h.g_lt v hv')
  rw [h.fg u hu', h.fg v hv'] at e1 e2
  rw [e1, e2, hw _ _ (h.g_lt u hu') (h.g_lt v hv')]

/-- The seed's sameness, writing included. -/
def SameW3 (G H : St) : Prop := ∃ f g, IsRw G.n f g ∧ Same3 (G.rename f) H

theorem Same3.sameW3 {G H : St} (h : Same3 G H) : SameW3 G H := ⟨id, id, IsRw.id _, by rw [rename_id]; exact h⟩

theorem SameW3.refl (G : St) : SameW3 G G := (Same3.refl G).sameW3

theorem SameW3.n {G H : St} (h : SameW3 G H) : G.n = H.n := by
  obtain ⟨_, _, _, s⟩ := h
  exact s.n

theorem SameW3.symm {G H : St} (h : SameW3 G H) (hG : G.WF) (hH : H.WF) : SameW3 H G := by
  obtain ⟨f, g, hr, s⟩ := h
  have hr' : IsRw (G.rename f).n g f := hr.symm
  have s' := s.rename hr' (rename_wf hr hG) hH
  rw [rename_rename hr hG] at s'
  exact ⟨g, f, s.n ▸ hr.symm, s'.symm⟩

theorem SameW3.trans {G H K : St} (h1 : SameW3 G H) (h2 : SameW3 H K) (hG : G.WF) (hH : H.WF) : SameW3 G K := by
  obtain ⟨f, g, hr, s⟩ := h1
  obtain ⟨f', g', hr', s'⟩ := h2
  have hr'' : IsRw (G.rename f).n f' g' := s.n ▸ hr'
  have t := s.rename hr'' (rename_wf hr hG) hH
  rw [rename_comp] at t
  exact ⟨f' ∘ f, g ∘ g', hr.comp (s.n ▸ hr'), t.trans s'⟩

/-- The sameness the seed's clauses generate, writing included. -/
inductive GenW3 : St → St → Prop
  | gen {G H : St} : Gen3 G H → GenW3 G H
  | rename (G : St) (f g : Nat → Nat) (h : IsRw G.n f g) (hw : G.WF) : GenW3 G (G.rename f)
  | symm {G H : St} : GenW3 G H → GenW3 H G
  | trans {G H K : St} : GenW3 G H → GenW3 H K → GenW3 G K

theorem Gen3.wf_iff {G H : St} (h : Gen3 G H) : G.WF ↔ H.WF := by
  induction h with
  | gen g => exact g.wf_iff
  | raise G x hx =>
    exact ⟨fun hw => raise_wf hx hw, fun hw a ha => hw a (List.mem_append_right _ ha)⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem GenW3.wf_iff {G H : St} (h : GenW3 G H) : G.WF ↔ H.WF := by
  induction h with
  | gen g => exact g.wf_iff
  | rename G f g h hw => exact ⟨fun _ => rename_wf h hw, fun _ => hw⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The full sameness is the equivalence the seed's clauses and rewriting generate** (well-formed states). -/
theorem genW3_iff_sameW3 {G H : St} (hG : G.WF) (hH : H.WF) : GenW3 G H ↔ SameW3 G H := by
  constructor
  · intro h
    induction h with
    | gen g => exact g.same3.sameW3
    | rename G f g h _ => exact ⟨f, g, h, Same3.refl _⟩
    | symm _ ih => exact (ih hH hG).symm hH hG
    | trans h1 h2 ih1 ih2 =>
      have hM := (h1.wf_iff).1 hG
      exact (ih1 hG hM).trans (ih2 hM hH) hG hM
  · rintro ⟨f, g, hr, s⟩
    exact GenW3.trans (GenW3.rename G f g hr hG) (GenW3.gen ((gen3_iff_same3 (rename_wf hr hG) hH).2 s))

/-- The fewest changes to a result, writing included. -/
def Cost3W (G : St) (c : Nat) : Prop :=
  (∃ H, SameW3 H G ∧ Reach empty H c) ∧ ∀ H k, SameW3 H G → Reach empty H k → c ≤ k

/-- **The cost of a result is the fewest changes to it in every writing.** -/
theorem cost3_every_writing {G : St} {c : Nat} (h : Cost3 G c) : Cost3W G c := by
  have hc := h
  obtain ⟨⟨H, s, r⟩, _⟩ := hc
  refine ⟨⟨H, s.sameW3, r⟩, fun K k sK rK => ?_⟩
  obtain ⟨f, g, hr, s'⟩ := sK
  have hK := rK.wf empty_wf
  have a := (cost3_iff.1 h).2 (K.rename f) (rename_wf hr hK) s'
  rw [phi_rename hr hK] at a
  have b := rK.phi_le
  rw [phi_empty] at b
  omega

/-- **The result asserting nothing is the same in every writing.** -/
theorem sameW3_nothing_iff {G : St} (hG : G.WF) : SameW3 G ⟨G.n, []⟩ ↔ Same3 G ⟨G.n, []⟩ := by
  constructor
  · rintro ⟨f, g, hr, s⟩
    have hr' : IsRw (G.rename f).n g f := hr.symm
    have t := s.rename hr' (rename_wf hr hG) (fun _ m => absurd m List.not_mem_nil)
    rw [rename_rename hr hG] at t
    exact t
  · exact Same3.sameW3

/-- **What a merge of twenty-second results loses**: `a b; arb bsa` and `a b` are one result here, while
their twenty-second costs (`phi`, 4 and 2), their excesses at `(a, b)` and their plain states differ; they
are two twenty-second results in every writing. -/
theorem merge_loses3 :
    Same3 raisedPair ⟨2, []⟩ ∧ phi raisedPair = 4 ∧ phi ⟨2, []⟩ = 2 ∧
      excess raisedPair 0 1 = 1 ∧ excess ⟨2, []⟩ 0 1 = 0 ∧ ¬ SameW raisedPair ⟨2, []⟩ := by
  refine ⟨raisedPair_nothing, by decide, rfl, by decide, rfl, fun h => ?_⟩
  have := h.phi (fun a ha => by
    simp only [raisedPair, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e <;> subst e <;> decide)
  exact absurd this (by decide)

/-- **On two terms, adding `xry` and then `ysx` gives back the result before both** (it is raising `x`):
two additions of two different pairs undo each other, which the twenty-second's sameness does not allow. -/
theorem two_additions_undo3 {G : St} (hn : G.n = 2) :
    Same3 ((G.add ⟨.s, 1, 0⟩).add ⟨.r, 0, 1⟩) G ∧ Same3 ((G.add ⟨.s, 0, 1⟩).add ⟨.r, 1, 0⟩) G := by
  have e0 : ((G.add ⟨.s, 1, 0⟩).add ⟨.r, 0, 1⟩) = raise G 0 := by
    cases G with
    | mk n A =>
      simp only at hn
      subst hn
      rfl
  have e1 : ((G.add ⟨.s, 0, 1⟩).add ⟨.r, 1, 0⟩) = raise G 1 := by
    cases G with
    | mk n A =>
      simp only at hn
      subst hn
      rfl
  rw [e0, e1]
  exact ⟨(same3_raise G 0).symm, (same3_raise G 1).symm⟩

end Twentythird
