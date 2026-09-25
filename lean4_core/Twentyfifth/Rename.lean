import Twentyfifth.Reach

/-!
# Rewriting the terms: the full sameness, with filled triples

A rewriting of the terms `0 … n − 1` is a one-to-one `f` with an inverse `g` on
them (the twenty-second's `IsRw`).  It rewrites the assertions (the
twenty-second's `St.rename`) and every filled triple, keeping the way round
(`FSt.rename`: each triple's terms moved by `f`, then written from the least).
`SameW25 A B`: some rewriting of `A` is `B` up to the sameness at a fixed
writing.

Derived here:
* a rewriting keeps a state well formed (`rename25_wf`), is undone by its
  inverse (`rename25_rename`), carries the sameness along (`Same25.rename`) and
  the sum around every filled triple (`around_rename`);
* `SameW25` is an equivalence (`SameW25.refl`, `SameW25.symm`, `SameW25.trans`)
  and is exactly what the seed's clauses and rewriting generate
  (`genW25_iff_sameW25`);
* **which filled triples balance, and so whether a result is told, is the same
  in every writing** (`SameW25.told_iff`); **the cost is the fewest changes in
  every writing** (`cost25_every_writing`);
* **the twenty-third maps one to one in every writing**
  (`embed_sameW_iff`); the two one-triple results on three terms are one
  result (`oneFilled_sameW_other`), so **the map back's smallest "none" is one
  result in every writing** (`readBack25_none_smallest_writing`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- A triple's terms moved by `f`, written from the least. -/
def Tri.rename (t : Tri) (f : Nat → Nat) : Tri := (t.map f).norm

/-- The state with its terms rewritten by `f`, in the assertions and in every filled triple. -/
def FSt.rename (A : FSt) (f : Nat → Nat) : FSt := ⟨A.G.rename f, A.F.map (fun t => t.rename f)⟩

theorem Tri.map_rot (f : Nat → Nat) (t : Tri) : t.rot.map f = (t.map f).rot := rfl

theorem Tri.map_map (f g : Nat → Nat) (t : Tri) : (t.map f).map g = t.map (g ∘ f) := rfl

/-- Moving the normal form of a moved triple is moving the triple, up to where it starts. -/
theorem Tri.norm_map_norm (f g : Nat → Nat) {t : Tri} (hd : (t.map (g ∘ f)).Distinct) :
    ((t.map f).norm.map g).norm = (t.map (g ∘ f)).norm := by
  rcases Tri.norm_cases (t.map f) with e | e | e <;> rw [e]
  · rfl
  · rw [Tri.map_rot, Tri.map_map, Tri.norm_rot hd]
  · rw [Tri.map_rot, Tri.map_rot, Tri.map_map, Tri.norm_rot (Tri.distinct_rot hd), Tri.norm_rot hd]

theorem Tri.distinct_map {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) {t : Tri} (hw : t.Within n)
    (hd : t.Distinct) : (t.map f).Distinct :=
  ⟨fun e => hd.1 (h.inj hw.1 hw.2.1 e), fun e => hd.2.1 (h.inj hw.2.1 hw.2.2 e),
    fun e => hd.2.2 (h.inj hw.1 hw.2.2 e)⟩

theorem Tri.within_map {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) {t : Tri} (hw : t.Within n) :
    (t.map f).Within n :=
  ⟨h.f_lt _ hw.1, h.f_lt _ hw.2.1, h.f_lt _ hw.2.2⟩

theorem Tri.map_gf {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) {t : Tri} (hw : t.Within n) :
    t.map (g ∘ f) = t := by
  obtain ⟨x, y, z⟩ := t
  show (⟨g (f x), g (f y), g (f z)⟩ : Tri) = ⟨x, y, z⟩
  rw [h.gf x hw.1, h.gf y hw.2.1, h.gf z hw.2.2]

/-- Rewriting a filled triple of a well-formed state, then rewriting back, gives the triple. -/
theorem Tri.rename_rename {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) {t : Tri} (hw : t.Within n)
    (hd : t.Distinct) (hn : t.norm = t) : (t.rename f).rename g = t := by
  unfold Tri.rename
  rw [Tri.norm_map_norm f g (by rw [Tri.map_gf h hw]; exact hd), Tri.map_gf h hw, hn]

theorem map_eq_self_tri {F : Tri → Tri} : ∀ l : List Tri, (∀ t ∈ l, F t = t) → l.map F = l
  | [], _ => rfl
  | t :: l, h => by
    rw [List.map_cons, h t List.mem_cons_self, map_eq_self_tri l (fun s hs => h s (List.mem_cons_of_mem _ hs))]

theorem nodup_map_of_inj {F : Tri → Tri} :
    ∀ {l : List Tri}, (∀ s ∈ l, ∀ t ∈ l, F s = F t → s = t) → l.Nodup → (l.map F).Nodup
  | [], _, _ => List.nodup_nil
  | s :: l, h, hn => by
    rw [List.map_cons]
    refine List.nodup_cons.2 ⟨fun m => ?_, nodup_map_of_inj (fun a ha b hb e =>
      h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) e) (List.nodup_cons.1 hn).2⟩
    obtain ⟨t, ht, e⟩ := List.mem_map.1 m
    have := h t (List.mem_cons_of_mem _ ht) s List.mem_cons_self e
    subst this
    exact (List.nodup_cons.1 hn).1 ht

/-- **A rewriting keeps a state well formed.** -/
theorem rename25_wf {A : FSt} {f g : Nat → Nat} (h : IsRw A.G.n f g) (hw : A.WF) : (A.rename f).WF := by
  refine ⟨rename_wf h hw.1, fun t ht => ?_, ?_⟩
  · obtain ⟨s, hs, e⟩ := List.mem_map.1 ht
    subst e
    obtain ⟨hsw, hsd, _⟩ := hw.2.1 s hs
    exact ⟨Tri.norm_within (Tri.within_map h hsw), Tri.norm_distinct (Tri.distinct_map h hsw hsd), Tri.norm_norm _⟩
  · refine nodup_map_of_inj (fun s hs t ht e => ?_) hw.2.2
    obtain ⟨hsw, hsd, hsn⟩ := hw.2.1 s hs
    obtain ⟨htw, htd, htn⟩ := hw.2.1 t ht
    have a := Tri.rename_rename h hsw hsd hsn
    have b := Tri.rename_rename h htw htd htn
    rw [← a, ← b]
    exact congrArg (fun u => Tri.rename u g) e

/-- **A rewriting is undone by its inverse.** -/
theorem rename25_rename {A : FSt} {f g : Nat → Nat} (h : IsRw A.G.n f g) (hw : A.WF) :
    (A.rename f).rename g = A := by
  cases A with
  | mk G F =>
    simp only [FSt.rename, List.map_map]
    congr 1
    · exact rename_rename h hw.1
    · apply map_eq_self_tri
      intro t ht
      obtain ⟨htw, htd, htn⟩ := hw.2.1 t ht
      exact Tri.rename_rename h htw htd htn

theorem rename25_comp {A : FSt} {f g f' g' : Nat → Nat} (h : IsRw A.G.n f g) (h' : IsRw A.G.n f' g')
    (hw : A.WF) : (A.rename f).rename f' = A.rename (f' ∘ f) := by
  cases A with
  | mk G F =>
    simp only [FSt.rename, List.map_map]
    congr 1
    · exact rename_comp G f f'
    · refine List.map_congr_left (fun t ht => ?_)
      obtain ⟨htw, htd, _⟩ := hw.2.1 t ht
      show ((t.map f).norm.map f').norm = (t.map (f' ∘ f)).norm
      exact Tri.norm_map_norm f f' (Tri.distinct_map (h.comp h') htw htd)

/-- **A rewriting carries the sum around every triple along.** -/
theorem around_rename {G : St} {f g : Nat → Nat} (h : IsRw G.n f g) (hw : G.WF) {t : Tri} (ht : t.Within G.n) :
    around (G.rename f) (t.rename f) = around G t := by
  unfold Tri.rename
  rw [around_norm]
  unfold around Tri.map
  rw [excess_rename h hw ht.1 ht.2.1, excess_rename h hw ht.2.1 ht.2.2, excess_rename h hw ht.2.2 ht.1]

theorem Same25.rename {A B : FSt} {f g : Nat → Nat} (s : Same25 A B) (h : IsRw A.G.n f g) (hA : A.WF)
    (hB : B.WF) : Same25 (A.rename f) (B.rename f) :=
  ⟨Same3.rename s.1 h hA.1 hB.1, s.2.map _⟩

/-- The seed's sameness, writing included. -/
def SameW25 (A B : FSt) : Prop := ∃ f g, IsRw A.G.n f g ∧ Same25 (A.rename f) B

theorem rename25_id (A : FSt) (hw : A.WF) : A.rename id = A := by
  cases A with
  | mk G F =>
    simp only [FSt.rename]
    congr 1
    · exact rename_id G
    · apply map_eq_self_tri
      intro t ht
      exact (hw.2.1 t ht).2.2

theorem Same25.sameW25 {A B : FSt} (hA : A.WF) (h : Same25 A B) : SameW25 A B :=
  ⟨id, id, IsRw.id _, by rw [rename25_id A hA]; exact h⟩

theorem SameW25.refl (A : FSt) (hA : A.WF) : SameW25 A A := (Same25.refl A).sameW25 hA

theorem SameW25.n {A B : FSt} (h : SameW25 A B) : A.G.n = B.G.n := by
  obtain ⟨_, _, _, s⟩ := h
  exact s.n

theorem SameW25.symm {A B : FSt} (h : SameW25 A B) (hA : A.WF) (hB : B.WF) : SameW25 B A := by
  obtain ⟨f, g, hr, s⟩ := h
  have hr' : IsRw (A.rename f).G.n g f := hr.symm
  have s' := s.rename hr' (rename25_wf hr hA) hB
  rw [rename25_rename hr hA] at s'
  exact ⟨g, f, s.n ▸ hr.symm, s'.symm⟩

theorem SameW25.trans {A B C : FSt} (h1 : SameW25 A B) (h2 : SameW25 B C) (hA : A.WF) (hB : B.WF) :
    SameW25 A C := by
  obtain ⟨f, g, hr, s⟩ := h1
  obtain ⟨f', g', hr', s'⟩ := h2
  have hr'' : IsRw (A.rename f).G.n f' g' := s.n ▸ hr'
  have t := s.rename hr'' (rename25_wf hr hA) hB
  have hr3 : IsRw A.G.n f' g' := s.n ▸ hr'
  rw [rename25_comp hr hr3 hA] at t
  exact ⟨f' ∘ f, g ∘ g', hr.comp hr3, t.trans s'⟩

/-- The sameness the seed's clauses and rewriting generate. -/
inductive GenW25 : FSt → FSt → Prop
  | gen {A B : FSt} : Gen25 A B → GenW25 A B
  | rename (A : FSt) (f g : Nat → Nat) (h : IsRw A.G.n f g) (hw : A.WF) : GenW25 A (A.rename f)
  | symm {A B : FSt} : GenW25 A B → GenW25 B A
  | trans {A B C : FSt} : GenW25 A B → GenW25 B C → GenW25 A C

theorem Gen25.wf_iff {A B : FSt} (h : Gen25 A B) : A.WF ↔ B.WF := by
  induction h with
  | @gen A B g e =>
    have hn : A.G.n = B.G.n := g.same3.n
    have hG := g.wf_iff
    constructor
    · rintro ⟨a, b, c⟩
      exact ⟨hG.1 a, fun t ht => by rw [← hn]; exact b t (e ▸ ht), e ▸ c⟩
    · rintro ⟨a, b, c⟩
      exact ⟨hG.2 a, fun t ht => by rw [hn]; exact b t (e ▸ ht), e ▸ c⟩
  | @perm A B e p =>
    constructor
    · rintro ⟨a, b, c⟩
      exact ⟨e ▸ a, fun t ht => e ▸ b t (p.mem_iff.2 ht), p.nodup_iff.1 c⟩
    · rintro ⟨a, b, c⟩
      exact ⟨e ▸ a, fun t ht => e.symm ▸ b t (p.mem_iff.1 ht), p.nodup_iff.2 c⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem GenW25.wf_iff {A B : FSt} (h : GenW25 A B) : A.WF ↔ B.WF := by
  induction h with
  | gen g => exact g.wf_iff
  | rename A f g h hw => exact ⟨fun _ => rename25_wf h hw, fun _ => hw⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The full sameness is the equivalence the seed's clauses and rewriting generate.** -/
theorem genW25_iff_sameW25 {A B : FSt} (hA : A.WF) (hB : B.WF) : GenW25 A B ↔ SameW25 A B := by
  constructor
  · intro h
    induction h with
    | gen g =>
      rename_i A' B'
      exact g.same25.sameW25 (by assumption)
    | rename A f g h _ => exact ⟨f, g, h, Same25.refl _⟩
    | symm _ ih => exact (ih hB hA).symm hB hA
    | trans h1 h2 ih1 ih2 =>
      have hM := (h1.wf_iff).1 hA
      exact (ih1 hA hM).trans (ih2 hM hB) hA hM
  · rintro ⟨f, g, hr, s⟩
    have hR := rename25_wf hr hA
    exact GenW25.trans (GenW25.rename A f g hr hA) (GenW25.gen ((gen25_iff_same25 hR.1 hB.1).2 s))

/-- Rewriting keeps whether a result is told. -/
theorem told_rename {A : FSt} {f g : Nat → Nat} (h : IsRw A.G.n f g) (hw : A.WF) : Told (A.rename f) ↔ Told A := by
  constructor
  · rintro ⟨u, hu, hn⟩
    obtain ⟨t, ht, e⟩ := List.mem_map.1 hu
    subst e
    refine ⟨t, ht, fun b => hn ?_⟩
    show around (A.G.rename f) (t.rename f) = 0
    rw [around_rename h hw.1 (hw.2.1 t ht).1]
    exact b
  · rintro ⟨t, ht, hn⟩
    refine ⟨t.rename f, List.mem_map_of_mem ht, fun b => hn ?_⟩
    change around (A.G.rename f) (t.rename f) = 0 at b
    rw [around_rename h hw.1 (hw.2.1 t ht).1] at b
    exact b

theorem Same25.told_iff {A B : FSt} (s : Same25 A B) (hA : A.WF) (hB : B.WF) : Told A ↔ Told B := by
  constructor
  · rintro ⟨t, ht, hn⟩
    obtain ⟨m, e⟩ := s.balanced_iff hA ht
    exact ⟨t, m, fun b => hn (e.2 b)⟩
  · rintro ⟨t, ht, hn⟩
    obtain ⟨m, e⟩ := s.symm.balanced_iff hB ht
    exact ⟨t, m, fun b => hn (e.2 b)⟩

/-- **Whether a result is told is the same in every writing.** -/
theorem SameW25.told_iff {A B : FSt} (h : SameW25 A B) (hA : A.WF) (hB : B.WF) : Told A ↔ Told B := by
  obtain ⟨f, g, hr, s⟩ := h
  exact (told_rename hr hA).symm.trans (s.told_iff (rename25_wf hr hA) hB)

/-- The fewest changes to a result, writing included. -/
def Cost25W (A : FSt) (c : Nat) : Prop :=
  (∃ B, SameW25 B A ∧ Reach25 empty25 B c) ∧ ∀ B k, SameW25 B A → Reach25 empty25 B k → c ≤ k

theorem psi_rename {A : FSt} {f g : Nat → Nat} (h : IsRw A.G.n f g) (hw : A.WF) : psi (A.rename f) = psi A := by
  simp only [psi, FSt.rename, List.length_map]
  rw [phi_rename h hw.1]

/-- **The cost is the fewest changes in every writing.** -/
theorem cost25_every_writing {c : Nat} {A : FSt} (h : Cost25 A c) : Cost25W A c := by
  have h0 := h
  obtain ⟨⟨B, s, r⟩, _⟩ := h0
  refine ⟨⟨B, s.sameW25 (r.wf empty25_wf), r⟩, fun K k sK rK => ?_⟩
  obtain ⟨f, g, hr, s'⟩ := sK
  have hK := rK.wf empty25_wf
  have a := ((Cost25.congr s'.symm).1 h).le_psi (rename25_wf hr hK)
  rw [psi_rename hr hK] at a
  have b := rK.psi_le
  rw [psi_empty25] at b
  omega

theorem embed_rename (G : St) (f : Nat → Nat) : (embed G).rename f = embed (G.rename f) := rfl

/-- **The twenty-third maps one to one in every writing.** -/
theorem embed_sameW_iff {G H : St} : SameW25 (embed G) (embed H) ↔ SameW3 G H := by
  constructor
  · rintro ⟨f, g, hr, s⟩
    rw [embed_rename] at s
    exact ⟨f, g, hr, embed_same_iff.1 s⟩
  · rintro ⟨f, g, hr, s⟩
    exact ⟨f, g, hr, by rw [embed_rename]; exact embed_same_iff.2 s⟩

/-- `b` and `c` exchanged, `a` kept. -/
def swapBC (t : Nat) : Nat := if t = 1 then 2 else if t = 2 then 1 else t

theorem swapBC_rw : IsRw 3 swapBC swapBC := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rcases lt_three hx with rfl | rfl | rfl <;> decide

/-- **The two one-triple results on three terms are one result**: `b` and `c` exchanged. -/
theorem oneFilled_sameW_other : SameW25 oneFilled oneFilledOther :=
  ⟨swapBC, swapBC, swapBC_rw, ⟨Same3.refl _, List.Perm.refl _⟩⟩

/-- **The map back's smallest "none" is one result in every writing**: every result it answers "none" on at
cost four is `a b c` with `a b c` filled and nothing asserted. -/
theorem readBack25_none_smallest_writing {A : FSt} (hA : A.WF) (h : readBack25 A = none) (hc : Cost25 A 4) :
    SameW25 A oneFilled := by
  rcases readBack25_none_smallest h hc with s | s
  · exact s.sameW25 hA
  · exact (s.sameW25 hA).trans ((oneFilled_sameW_other).symm oneFilled_wf oneFilledOther_wf) hA
      oneFilledOther_wf

end Twentyfifth
