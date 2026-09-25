import Twentysecond.Plain

/-!
# The seed's sameness, at a fixed writing of the terms

The changed sentence: "Two results that differ only in how their terms are
written, or only by an `xry` and an `xsy` asserted together, are the same
result."  Here the terms keep their writing (rewriting is `Rename.lean`).

`Gen` is the sameness the sentence generates at a fixed writing (reading C-J1
of the paper): the same state (a rearranged list), or one state with one more
`xry` and one more `xsy` on the same two terms, closed under symmetry and
transitivity — "are the same result" is an equivalence.

`Same G H`: equally many terms and the same plain part.  Derived:
* `gen_iff_same`: for well-formed states the generated sameness *is* `Same`;
* `same_iff_excess`: `Same` is "equally many terms and the same excess
  `M_r(x, y) − M_s(x, y)` at every ordered pair";
* congruences: adding a term, adding an assertion, identifying two terms
  respect `Same`; removing an atom from two same states respects it when both
  assert it (`Same.remove`), and removing `xry` is the same result as adding
  `xsy` (`same_remove_add_partner`);
* `step_of_same`: **a change of any state of a result has the outcome of a
  change of any other state of it** (reading C-X): the results one change
  away do not depend on which state is taken.
-/

namespace Twentysecond

/-- The seed's sameness at a fixed writing: equally many terms, the same plain part. -/
def Same (G H : St) : Prop := G.n = H.n ∧ (plain G.A).Perm (plain H.A)

theorem Same.refl (G : St) : Same G G := ⟨rfl, List.Perm.refl _⟩

theorem Same.symm {G H : St} (h : Same G H) : Same H G := ⟨h.1.symm, h.2.symm⟩

theorem Same.trans {G H K : St} (h1 : Same G H) (h2 : Same H K) : Same G K :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem SameState9.same {G H : St} (h : SameState9 G H) : Same G H := ⟨h.1, plain_perm h.2⟩

/-- The excess of `x r y` over `x s y`. -/
def excess (G : St) (x y : Nat) : Int :=
  (G.A.count ⟨.r, x, y⟩ : Int) - (G.A.count ⟨.s, x, y⟩ : Int)

/-- **Same result at a fixed writing = equally many terms and the same excess at every pair.** -/
theorem same_iff_excess {G H : St} : Same G H ↔ G.n = H.n ∧ ∀ x y, excess G x y = excess H x y := by
  unfold Same excess
  rw [plain_perm_iff]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun x y => ?_⟩
    have := h ⟨.r, x, y⟩
    simp only [Atom.partner, Rel.other] at this
    omega
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun b => ?_⟩
    obtain ⟨q, x, y⟩ := b
    have := h x y
    cases q
    · simp only [Atom.partner, Rel.other]
      omega
    · simp only [Atom.partner, Rel.other]
      omega

/-- The sameness the changed sentence generates, at a fixed writing of the terms. -/
inductive Gen : St → St → Prop
  | perm {G H : St} : G.n = H.n → G.A.Perm H.A → Gen G H
  | pair (G : St) (x y : Nat) (hx : x < G.n) (hy : y < G.n) :
      Gen G ⟨G.n, ⟨.r, x, y⟩ :: ⟨.s, x, y⟩ :: G.A⟩
  | symm {G H : St} : Gen G H → Gen H G
  | trans {G H K : St} : Gen G H → Gen H K → Gen G K

theorem Gen.same {G H : St} (h : Gen G H) : Same G H := by
  induction h with
  | perm hn hp => exact ⟨hn, plain_perm hp⟩
  | pair G x y _ _ =>
    refine ⟨rfl, ?_⟩
    apply List.Perm.symm
    apply plain_perm_iff.2
    intro b
    rw [count_cons', count_cons', count_cons', count_cons']
    obtain ⟨q, bx, by'⟩ := b
    cases q <;> simp [Atom.partner, Rel.other] <;> omega
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Taking out pairs asserted together, one pair at a time. -/
theorem gen_strip {n : Nat} {M : List Atom} (hM : Together M) (hw : ∀ a ∈ M, a.x < n ∧ a.y < n) :
    ∀ X : List Atom, Gen ⟨n, X ++ M⟩ ⟨n, X⟩ := by
  induction hM with
  | nil => intro X; rw [List.append_nil]; exact Gen.perm rfl (List.Perm.refl _)
  | @cons a M' _ ih =>
    intro X
    have ha := hw a List.mem_cons_self
    have hrest : ∀ b ∈ M', b.x < n ∧ b.y < n :=
      fun b hb => hw b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))
    have step : Gen ⟨n, X ++ a :: a.partner :: M'⟩ ⟨n, X ++ M'⟩ := by
      have p1 : (X ++ a :: a.partner :: M').Perm (a :: a.partner :: (X ++ M')) :=
        List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      refine Gen.trans (H := ⟨n, a :: a.partner :: (X ++ M')⟩) (Gen.perm rfl p1) ?_
      obtain ⟨q, x, y⟩ := a
      cases q
      · exact Gen.symm (Gen.pair ⟨n, X ++ M'⟩ x y ha.1 ha.2)
      · refine Gen.trans (H := ⟨n, ⟨.r, x, y⟩ :: ⟨.s, x, y⟩ :: (X ++ M')⟩)
          (Gen.perm rfl (List.Perm.swap _ _ _)) ?_
        exact Gen.symm (Gen.pair ⟨n, X ++ M'⟩ x y ha.1 ha.2)
    exact Gen.trans step (ih hrest X)

/-- A well-formed state is, by the generated sameness, its plain part. -/
theorem gen_plain {G : St} (hw : G.WF) : Gen G ⟨G.n, plain G.A⟩ := by
  refine Gen.trans (H := ⟨G.n, plain G.A ++ together G.A⟩) (Gen.perm rfl (perm_split G.A)) ?_
  exact gen_strip (together_together G.A) (fun a ha => hw a (mem_of_mem_together ha)) (plain G.A)

/-- **The sameness the changed sentence generates is `Same`** (well-formed states). -/
theorem gen_iff_same {G H : St} (hG : G.WF) (hH : H.WF) : Gen G H ↔ Same G H := by
  constructor
  · exact Gen.same
  · intro h
    refine Gen.trans (gen_plain hG) (Gen.trans (H := ⟨H.n, plain H.A⟩) (Gen.perm h.1 h.2) (Gen.symm ?_))
    exact gen_plain hH

/-- The same plain part as a state. -/
def St.plainSt (G : St) : St := ⟨G.n, plain G.A⟩

theorem same_plainSt (G : St) : Same G G.plainSt := ⟨rfl, by rw [St.plainSt, plain_plain]⟩

theorem plainSt_wf {G : St} (hw : G.WF) : G.plainSt.WF := fun a ha => hw a (mem_of_mem_plain ha)

/-! ## Congruences -/

theorem Same.addTerm {G H : St} (h : Same G H) : Same G.addTerm H.addTerm :=
  ⟨by simp [St.addTerm, h.1], h.2⟩

theorem Same.add {G H : St} (h : Same G H) (a : Atom) : Same (G.add a) (H.add a) :=
  ⟨h.1, plain_cons_perm a h.2⟩

theorem Same.identify {G H : St} (h : Same G H) (u v : Nat) : Same (G.identify u v) (H.identify u v) := by
  refine ⟨by simp [St.identify, h.1], ?_⟩
  simp only [St.identify, h.1]
  refine (plain_map_perm _ G.A).trans ?_
  refine List.Perm.trans ?_ (plain_map_perm _ H.A).symm
  exact plain_perm (h.2.map _)

theorem count_del_add {a : Atom} {l : List Atom} (h : a ∈ l) (b : Atom) :
    (del a l).count b + (if b = a then 1 else 0) = l.count b := by
  have := (perm_cons_del h).count_eq b
  rw [this, count_cons']
  by_cases e : b = a
  · subst e; simp
  · have : a ≠ b := Ne.symm e
    simp [e, this]

theorem ite_partner_partner (a b : Atom) :
    (if a.partner = b.partner then 1 else 0 : Nat) = (if b = a then 1 else 0) := by
  by_cases h : b = a
  · subst h
    simp
  · have : a.partner ≠ b.partner := fun e => h (Atom.partner_inj e).symm
    simp [h, this]

theorem ite_partner_left (a b : Atom) :
    (if a.partner = b then 1 else 0 : Nat) = (if b.partner = a then 1 else 0) := by
  by_cases h : b.partner = a
  · subst h
    simp
  · have : a.partner ≠ b := fun e => h (by rw [← e, Atom.partner_partner])
    simp [h, this]

/-- Removing `xry` is the same result as adding `xsy`. -/
theorem same_remove_add_partner {G : St} {a : Atom} (h : a ∈ G.A) : Same (G.remove a) (G.add a.partner) := by
  refine ⟨rfl, plain_perm_iff.2 fun b => ?_⟩
  simp only [St.remove, St.add]
  have e1 := count_del_add h b
  have e2 := count_del_add h b.partner
  rw [count_cons', count_cons', ite_partner_partner, ite_partner_left]
  omega

theorem Same.remove {G H : St} (h : Same G H) {a : Atom} (hG : a ∈ G.A) (hH : a ∈ H.A) :
    Same (G.remove a) (H.remove a) := by
  refine ⟨h.1, plain_perm_iff.2 fun b => ?_⟩
  have e := plain_perm_iff.1 h.2 b
  simp only [St.remove]
  have g1 := count_del_add hG b
  have g2 := count_del_add hG b.partner
  have h1 := count_del_add hH b
  have h2 := count_del_add hH b.partner
  omega

/-- **The outcome of a change of any state of a result is, up to the seed's sameness, the outcome of
a change of any other state of that result** (reading C-X). -/
theorem step_of_same {G H G' : St} (hs : Same G H) (hG : G.WF) (st : Step G G') :
    ∃ H', Step H H' ∧ Same G' H' := by
  cases st with
  | addTerm => exact ⟨H.addTerm, Step.addTerm H, hs.addTerm⟩
  | add a hx hy => exact ⟨H.add a, Step.add H a (hs.1 ▸ hx) (hs.1 ▸ hy), hs.add a⟩
  | remove a ha =>
    by_cases hH : a ∈ H.A
    · exact ⟨H.remove a, Step.remove H a hH, hs.remove ha hH⟩
    · have hx := (hG a ha).1
      have hy := (hG a ha).2
      refine ⟨H.add a.partner, Step.add H a.partner (hs.1 ▸ hx) (hs.1 ▸ hy), ?_⟩
      exact (same_remove_add_partner ha).trans (hs.add a.partner)
  | identify u v hu hv huv =>
    exact ⟨H.identify u v, Step.identify H u v (hs.1 ▸ hu) (hs.1 ▸ hv) huv, hs.identify u v⟩

end Twentysecond
