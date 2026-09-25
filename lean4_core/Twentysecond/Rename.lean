import Twentysecond.Swap

/-!
# Rewriting the terms: the full sameness

"Two results that differ only in how their terms are written, or only by an
`xry` and an `xsy` asserted together, are the same result."  A rewriting of
the terms `0 … n − 1` is a one-to-one `f` with an inverse `g` on them
(`IsRw`).  `SameW G H`: some rewriting of `G` has the same plain part as `H`.

Derived here:
* the plain part is carried along by a rewriting (`plain_rename`), so `phi`
  and the sameness are (`phi_rename`, `Same.rename`);
* `SameW` is an equivalence (`SameW.refl`, `SameW.symm`, `SameW.trans`) and
  is exactly the equivalence the sentence generates from its two clauses
  (`genW_iff_sameW`);
* the fewest changes to a result, writing included, is `phi`
  (`fewest_changes_every_writing`);
* the ninth's size is the same in every writing, so a non-empty sequence of
  additions never returns to its start's ninth result in any writing
  (`ninth_additions_never_return_every_writing`);
* **the seventh's states map one to one in every writing**: two seventh
  states give the same result here exactly when a rewriting makes them the
  same seventh state (`ofR_sameW_iff`); the map back answers "none" on the
  same results in every writing (`readBack_none_rename`).
-/

namespace Twentysecond

/-- `f` rewrites the terms `0 … n − 1` one to one, `g` being its inverse. -/
structure IsRw (n : Nat) (f g : Nat → Nat) : Prop where
  f_lt : ∀ x, x < n → f x < n
  g_lt : ∀ x, x < n → g x < n
  gf : ∀ x, x < n → g (f x) = x
  fg : ∀ x, x < n → f (g x) = x

theorem IsRw.id (n : Nat) : IsRw n id id := ⟨fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl⟩

theorem IsRw.symm {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) : IsRw n g f := ⟨h.g_lt, h.f_lt, h.fg, h.gf⟩

theorem IsRw.comp {n : Nat} {f g f' g' : Nat → Nat} (h : IsRw n f g) (h' : IsRw n f' g') :
    IsRw n (f' ∘ f) (g ∘ g') :=
  ⟨fun x hx => h'.f_lt _ (h.f_lt x hx), fun x hx => h.g_lt _ (h'.g_lt x hx),
    fun x hx => by simp only [Function.comp]; rw [h'.gf _ (h.f_lt x hx), h.gf x hx],
    fun x hx => by simp only [Function.comp]; rw [h.fg _ (h'.g_lt x hx), h'.fg x hx]⟩

theorem IsRw.inj {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) {x y : Nat} (hx : x < n) (hy : y < n)
    (e : f x = f y) : x = y := by
  rw [← h.gf x hx, ← h.gf y hy, e]

/-- The state with its terms rewritten by `f`. -/
def St.rename (G : St) (f : Nat → Nat) : St := ⟨G.n, G.A.map (Atom.mapT f)⟩

theorem mapT_inj {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) {a b : Atom}
    (ha : a.x < n ∧ a.y < n) (hb : b.x < n ∧ b.y < n) (e : a.mapT f = b.mapT f) : a = b := by
  obtain ⟨q, x, y⟩ := a
  obtain ⟨q', x', y'⟩ := b
  simp only [Atom.mapT, Atom.mk.injEq] at e
  simp only at ha hb
  rw [e.1, h.inj ha.1 hb.1 e.2.1, h.inj ha.2 hb.2 e.2.2]

theorem map_del_of_injOn {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β} (a : α) :
    ∀ l : List α, (∀ c ∈ l, f c = f a → c = a) → (del a l).map f = del (f a) (l.map f)
  | [], _ => rfl
  | c :: t, hf => by
    by_cases e : c = a
    · subst e
      rw [del_cons_self, List.map_cons, del_cons_self]
    · have : f c ≠ f a := fun h => e (hf c List.mem_cons_self h)
      rw [del_cons_ne _ e, List.map_cons, List.map_cons, del_cons_ne _ this,
        map_del_of_injOn a t (fun d hd => hf d (List.mem_cons_of_mem _ hd))]

/-- **A rewriting carries the plain part along.** -/
theorem plain_rename {n : Nat} {f g : Nat → Nat} (h : IsRw n f g) :
    ∀ l : List Atom, (∀ a ∈ l, a.x < n ∧ a.y < n) → plain (l.map (Atom.mapT f)) = (plain l).map (Atom.mapT f)
  | [], _ => rfl
  | a :: t, hl => by
    have ht : ∀ b ∈ t, b.x < n ∧ b.y < n := fun b hb => hl b (List.mem_cons_of_mem _ hb)
    have ha : a.partner.x < n ∧ a.partner.y < n := hl a List.mem_cons_self
    have ih := plain_rename h t ht
    have hpl : ∀ c ∈ plain t, c.x < n ∧ c.y < n := fun c hc => ht c (mem_of_mem_plain hc)
    rw [List.map_cons, plain_cons, plain_cons, ih, Atom.mapT_partner]
    by_cases hm : a.partner ∈ plain t
    · have hm' : a.partner.mapT f ∈ (plain t).map (Atom.mapT f) := List.mem_map_of_mem hm
      rw [if_pos hm', if_pos hm]
      exact (map_del_of_injOn a.partner (plain t)
        (fun c hc e => mapT_inj h (hpl c hc) ha e)).symm
    · have hm' : a.partner.mapT f ∉ (plain t).map (Atom.mapT f) := by
        intro m
        obtain ⟨c, hc, e⟩ := List.mem_map.1 m
        exact hm (mapT_inj h (hpl c hc) ha e ▸ hc)
      rw [if_neg hm', if_neg hm]
      rfl

theorem rename_wf {G : St} {f g : Nat → Nat} (h : IsRw G.n f g) (hw : G.WF) : (G.rename f).WF := by
  intro a ha
  obtain ⟨c, hc, e⟩ := List.mem_map.1 ha
  subst e
  exact ⟨h.f_lt _ (hw c hc).1, h.f_lt _ (hw c hc).2⟩

theorem map_eq_self {F : Atom → Atom} : ∀ l : List Atom, (∀ a ∈ l, F a = a) → l.map F = l
  | [], _ => rfl
  | a :: t, h => by
    rw [List.map_cons, h a List.mem_cons_self, map_eq_self t (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem rename_rename {G : St} {f g : Nat → Nat} (h : IsRw G.n f g) (hw : G.WF) :
    (G.rename f).rename g = G := by
  cases G with
  | mk n A =>
    simp only [St.rename, List.map_map]
    congr 1
    apply map_eq_self
    intro a ha
    obtain ⟨q, x, y⟩ := a
    simp only [Function.comp, Atom.mapT]
    rw [h.gf x (hw _ ha).1, h.gf y (hw _ ha).2]

theorem rename_comp (G : St) (f f' : Nat → Nat) : (G.rename f).rename f' = G.rename (f' ∘ f) := by
  simp only [St.rename, List.map_map]
  rfl

theorem rename_id (G : St) : G.rename id = G := by
  cases G with
  | mk n A =>
    simp only [St.rename]
    congr 1
    exact map_eq_self A (fun a _ => rfl)

theorem Same.rename {G H : St} {f g : Nat → Nat} (h : Same G H) (hf : IsRw G.n f g) (hG : G.WF) (hH : H.WF) :
    Same (G.rename f) (H.rename f) := by
  refine ⟨h.1, ?_⟩
  simp only [St.rename]
  rw [plain_rename hf G.A hG, plain_rename (h.1 ▸ hf) H.A hH]
  exact h.2.map _

theorem phi_rename {G : St} {f g : Nat → Nat} (hf : IsRw G.n f g) (hw : G.WF) : phi (G.rename f) = phi G := by
  simp only [phi, St.rename]
  rw [plain_rename hf G.A hw, List.length_map]

theorem size_rename (G : St) (f : Nat → Nat) : (G.rename f).size = G.size := by
  simp [St.size, St.rename]

/-- The seed's sameness, writing included. -/
def SameW (G H : St) : Prop := ∃ f g, IsRw G.n f g ∧ Same (G.rename f) H

theorem SameW.n {G H : St} (h : SameW G H) : G.n = H.n := by
  obtain ⟨_, _, _, s⟩ := h
  exact s.1

theorem Same.sameW {G H : St} (h : Same G H) : SameW G H := ⟨id, id, IsRw.id _, by rw [rename_id]; exact h⟩

theorem SameW.refl (G : St) : SameW G G := (Same.refl G).sameW

theorem SameW.symm {G H : St} (h : SameW G H) (hG : G.WF) (hH : H.WF) : SameW H G := by
  obtain ⟨f, g, hr, s⟩ := h
  have hr' : IsRw (G.rename f).n g f := hr.symm
  have s' := s.rename hr' (rename_wf hr hG) hH
  rw [rename_rename hr hG] at s'
  exact ⟨g, f, s.1 ▸ hr.symm, s'.symm⟩

theorem SameW.trans {G H K : St} (h1 : SameW G H) (h2 : SameW H K) (hG : G.WF) (hH : H.WF) : SameW G K := by
  obtain ⟨f, g, hr, s⟩ := h1
  obtain ⟨f', g', hr', s'⟩ := h2
  have hr'' : IsRw (G.rename f).n f' g' := s.1 ▸ hr'
  have t := s.rename hr'' (rename_wf hr hG) hH
  rw [rename_comp] at t
  exact ⟨f' ∘ f, g ∘ g', hr.comp (s.1 ▸ hr'), t.trans s'⟩

theorem SameW.phi {G H : St} (h : SameW G H) (hG : G.WF) : phi G = phi H := by
  obtain ⟨f, g, hr, s⟩ := h
  rw [← phi_rename hr hG, s.phi]

/-- The sameness the changed sentence generates from its two clauses, writing included. -/
inductive GenW : St → St → Prop
  | gen {G H : St} : Gen G H → GenW G H
  | rename (G : St) (f g : Nat → Nat) (h : IsRw G.n f g) (hw : G.WF) : GenW G (G.rename f)
  | symm {G H : St} : GenW G H → GenW H G
  | trans {G H K : St} : GenW G H → GenW H K → GenW G K

theorem Gen.wf_iff {G H : St} (h : Gen G H) : G.WF ↔ H.WF := by
  induction h with
  | perm hn hp =>
    constructor
    · intro hw a ha
      rw [← hn]
      exact hw a (hp.symm.mem_iff.1 ha)
    · intro hw a ha
      rw [hn]
      exact hw a (hp.mem_iff.1 ha)
  | pair G x y hx hy =>
    constructor
    · intro hw a ha
      rcases List.mem_cons.1 ha with e | ha'
      · subst e; exact ⟨hx, hy⟩
      · rcases List.mem_cons.1 ha' with e | ha''
        · subst e; exact ⟨hx, hy⟩
        · exact hw a ha''
    · intro hw a ha
      exact hw a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem GenW.wf_iff {G H : St} (h : GenW G H) : G.WF ↔ H.WF := by
  induction h with
  | gen g => exact g.wf_iff
  | rename G f g h hw => exact ⟨fun _ => rename_wf h hw, fun _ => hw⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The full sameness is the equivalence the changed sentence generates** (well-formed states). -/
theorem genW_iff_sameW {G H : St} (hG : G.WF) (hH : H.WF) : GenW G H ↔ SameW G H := by
  constructor
  · intro h
    induction h with
    | gen g => exact g.same.sameW
    | rename G f g h _ => exact ⟨f, g, h, Same.refl _⟩
    | symm _ ih =>
      exact (ih hH hG).symm hH hG
    | trans h1 h2 ih1 ih2 =>
      have hM := (h1.wf_iff).1 hG
      exact (ih1 hG hM).trans (ih2 hM hH) hG hM
  · rintro ⟨f, g, hr, s⟩
    exact GenW.trans (GenW.rename G f g hr hG)
      (GenW.gen ((gen_iff_same (rename_wf hr hG) hH).2 s))

/-- **The fewest changes to a result, writing included, is `phi`.** -/
theorem fewest_changes_every_writing {G : St} (hw : G.WF) :
    (∃ H, SameW H G ∧ Reach empty H (phi G)) ∧
      ∀ H k, SameW H G → Reach empty H k → phi G ≤ k := by
  refine ⟨⟨G.plainSt, (same_plainSt G).symm.sameW, (reach_plainSt hw).reach⟩, ?_⟩
  intro H k hs r
  have hH := r.wf empty_wf
  have := r.phi_le
  rw [phi_empty, hs.phi hH] at this
  omega

/-- The ninth's sameness, writing included: a rewriting of `G` is the same ninth state as `H`. -/
def SameW9 (G H : St) : Prop := ∃ f g, IsRw G.n f g ∧ SameState9 (G.rename f) H

/-- **In the ninth, in every writing, a non-empty sequence of additions never returns to its
start's result.** -/
theorem ninth_additions_never_return_every_writing {G H : St} {k : Nat} (r : AddReach G H k) (hk : 0 < k) :
    ¬ SameW9 G H := by
  rintro ⟨f, _, _, s⟩
  have e1 := s.size
  have e2 := r.size
  rw [size_rename] at e1
  omega

/-- A list with no pair taken out is its own plain part. -/
theorem plain_eq_self_of_together_nil : ∀ {l : List Atom}, together l = [] → plain l = l
  | [], _ => rfl
  | a :: t, h => by
    rw [together_cons] at h
    by_cases hm : a.partner ∈ plain t
    · rw [if_pos hm] at h
      exact absurd h (List.cons_ne_nil _ _)
    · rw [if_neg hm] at h
      rw [plain_cons, if_neg hm, plain_eq_self_of_together_nil h]

/-- A rewriting of a state asserting no pair in both relations asserts none either. -/
theorem together_rename_nil {G : St} {f g : Nat → Nat} (hr : IsRw G.n f g) (hw : G.WF)
    (h : together G.A = []) : together (G.rename f).A = [] := by
  apply together_eq_nil_of_plain
  simp only [St.rename]
  rw [plain_rename hr G.A hw, plain_eq_self_of_together_nil h]

/-- **The ninth's results asserting no pair in both relations stay different here, in every
writing.** -/
theorem plain_states_stay_apart_every_writing {G H : St} (hG : G.WF) (tG : together G.A = [])
    (tH : together H.A = []) : SameW G H ↔ SameW9 G H := by
  constructor
  · rintro ⟨f, g, hr, s⟩
    exact ⟨f, g, hr, (plain_states_stay_apart (together_rename_nil hr hG tG) tH).1 s⟩
  · rintro ⟨f, g, hr, s⟩
    exact ⟨f, g, hr, s.same⟩

/-! ## The seventh's states in every writing -/

/-- The seventh state with its terms rewritten by `f`. -/
def St7.rename (M : St7) (f : Nat → Nat) : St7 := ⟨M.n, M.P.map (fun p => (f p.1, f p.2))⟩

/-- The seventh's sameness, writing included. -/
def SameW7 (M M' : St7) : Prop := ∃ f g, IsRw M.n f g ∧ SameState7 (M.rename f) M'

theorem ofR_rename (M : St7) (f : Nat → Nat) : ofR (M.rename f) = (ofR M).rename f := by
  simp only [ofR, St7.rename, St.rename, List.map_map]
  rfl

/-- **The seventh's states map one to one into this seed's results, in every writing.** -/
theorem ofR_sameW_iff {M M' : St7} : SameW (ofR M) (ofR M') ↔ SameW7 M M' := by
  constructor
  · rintro ⟨f, g, hr, s⟩
    rw [← ofR_rename] at s
    exact ⟨f, g, hr, ofR_same_iff.1 s⟩
  · rintro ⟨f, g, hr, s⟩
    refine ⟨f, g, hr, ?_⟩
    rw [← ofR_rename]
    exact ofR_same_iff.2 s

/-- The map back answers "none" on the same results in every writing. -/
theorem readBack_none_rename {G : St} {f g : Nat → Nat} (hr : IsRw G.n f g) (hw : G.WF) :
    readBack (G.rename f) = none ↔ readBack G = none := by
  have key : ∀ l : List Atom, rParts (l.map (Atom.mapT f)) = none ↔ rParts l = none := by
    intro l
    induction l with
    | nil => simp [rParts]
    | cons a t ih =>
      obtain ⟨q, x, y⟩ := a
      cases q with
      | s => simp [rParts, Atom.mapT]
      | r =>
        simp only [List.map_cons, Atom.mapT]
        cases h1 : rParts t with
        | none =>
          have h2 : rParts (t.map (Atom.mapT f)) = none := ih.2 h1
          simp [rParts, h1, h2]
        | some P =>
          cases h2 : rParts (t.map (Atom.mapT f)) with
          | none => rw [h1] at ih; exact absurd (ih.1 h2) (by simp)
          | some P' => simp [rParts, h1, h2]
  unfold readBack
  simp only [St.rename]
  rw [plain_rename hr G.A hw]
  constructor
  · intro h
    cases e : rParts (plain G.A) with
    | none => rfl
    | some P =>
      cases e' : rParts ((plain G.A).map (Atom.mapT f)) with
      | none => rw [key] at e'; rw [e] at e'; exact absurd e' (by simp)
      | some P' => rw [e'] at h; exact absurd h (by simp)
  · intro h
    cases e : rParts (plain G.A) with
    | none =>
      have := (key (plain G.A)).2 e
      rw [this]
    | some P => rw [e] at h; exact absurd h (by simp)

end Twentysecond
