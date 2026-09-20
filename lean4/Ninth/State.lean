import Eighth.Rename

/-!
# The ninth seed: two relations, nothing given

`prompt/ninth/seed_prompt.md` is the eighth seed (two relations `r` and `s`
between the same terms) with the seventh's beginning: "Nothing is given: to
begin with there are no terms and nothing is asserted."  There is no `a`, no
`b`, no `arb`.  The eighth's `DSt` carries the two names as fields and its `WF`
puts them among the terms, so a state without terms is not well formed there:
the ninth seed needs a two-relation state without names.

* `NDSt`: terms and a multiplicity function for each relation.  `WF`, `size`
  and the four operations are the eighth's definitions with the names left out;
  `swap` exchanges the two relations.
* `empty9`: the beginning.
* Four maps connect this model to the two it composes, all needed to cite the
  earlier results and to say whether they survive with nothing given *and* two
  relations:
  - `DSt.forget`: an eighth state with its names dropped;
  - `NDSt.name s c`: a ninth state with both names put on the term `c`, well
    formed exactly when `c` is a term (`name9_wf`, `wf_of_name9`);
  - `NDSt.proj q`: the `r` part or the `s` part, a state of the seventh seed;
  - `NSt.ofR`: a seventh state read as a ninth state asserting nothing with `s`.
  Forgetting after naming gives the state back (`forget_name9`), the
  operations commute with every map definitionally or by one `Function.update`
  lemma each, and the size is the same on both sides of `name` and `forget`
  (`size_name9`, `size_forget9`).

Derived here: the empty state is well formed and has size 0; a well-formed
state without terms is the empty state (`eq_empty9_of_wf`); adding a term to a
well-formed state raises its size by one (`size_addTerm9`, the seventh's
`size_addTerm7` on both parts); the size is the seventh's size of the `r` part
plus the `s` total (`size9_eq`, definitional), and exchanging the relations
keeps it (`size9_swap`).
-/

namespace Seed.Ninth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth

/-- A state of the ninth seed: terms and a multiplicity for each ordered pair in each relation.
No names. -/
@[ext]
structure NDSt where
  T : Finset ℕ
  M : Rel → ℕ × ℕ → ℕ

namespace NDSt

/-- The `r` part (`q = false`) or the `s` part (`q = true`): a state of the seventh seed. -/
def proj (s : NDSt) (q : Rel) : NSt := ⟨s.T, s.M q⟩

/-- Both parts are well formed (they share the terms). -/
def WF (s : NDSt) : Prop := (s.proj false).WF ∧ (s.proj true).WF

/-- Nothing is asserted with relation `q`. -/
def NothingIn (s : NDSt) (q : Rel) : Prop := ∀ p, s.M q p = 0

/-- Adding a term (to both relations at once, since they share the terms). -/
def addTerm (s : NDSt) (t : ℕ) : NDSt := ⟨insert t s.T, s.M⟩

/-- Adding an assertion of relation `q`: its multiplicity rises by one. -/
def addAssertion (s : NDSt) (q : Rel) (x y : ℕ) : NDSt :=
  ⟨s.T, Function.update s.M q (Function.update (s.M q) (x, y) (s.M q (x, y) + 1))⟩

/-- Removing an assertion of relation `q`: its multiplicity falls by one. -/
def remove (s : NDSt) (q : Rel) (x y : ℕ) : NDSt :=
  ⟨s.T, Function.update s.M q (Function.update (s.M q) (x, y) (s.M q (x, y) - 1))⟩

/-- Identifying `u` and `v` in every assertion of both relations; the multiplicities of the
pairs that become one pair add up, in each relation separately. -/
def identify (s : NDSt) (u v : ℕ) : NDSt :=
  ⟨s.T.erase v,
    fun q p => ∑ w ∈ (s.T ×ˢ s.T).filter (fun w => (merge u v w.1, merge u v w.2) = p), s.M q w⟩

/-- Terms plus the assertions of both relations, counted with multiplicity: the seventh's size
of the `r` part plus the `s` total. -/
def size (s : NDSt) : ℕ := (s.proj false).size + (s.proj true).total

/-- The state read as a state of the eighth seed, both names on the term `c`. -/
def name (s : NDSt) (c : ℕ) : DSt := ⟨s.T, s.M, c, c⟩

/-- The two relations exchanged: every `xry` read as `xsy` and the converse. -/
def swap (s : NDSt) : NDSt := ⟨s.T, fun q => s.M (!q)⟩

end NDSt

open NDSt

/-- What is given: no terms, nothing asserted in either relation. -/
def empty9 : NDSt := ⟨∅, fun _ _ => 0⟩

/-- A state of the eighth seed with its names forgotten. -/
def _root_.Seed.Eighth.DSt.forget (s : DSt) : NDSt := ⟨s.T, s.M⟩

/-- A state of the seventh seed read as a two-relation state asserting nothing with `s`. -/
def _root_.Seed.Seventh.NSt.ofR (m : NSt) : NDSt :=
  ⟨m.T, fun q => match q with
    | false => m.M
    | true => fun _ => 0⟩

/-! ## Projections -/

@[simp] theorem proj9_T (s : NDSt) (q : Rel) : (s.proj q).T = s.T := rfl
@[simp] theorem proj9_M (s : NDSt) (q : Rel) : (s.proj q).M = s.M q := rfl

/-- A two-relation state is determined by its two parts. -/
theorem ext_proj9 {s t : NDSt} (h : ∀ q, s.proj q = t.proj q) : s = t := by
  apply NDSt.ext
  · exact congrArg NSt.T (h false)
  · funext q
    exact congrArg NSt.M (h q)

theorem proj9_addTerm (s : NDSt) (t : ℕ) (q : Rel) : (s.addTerm t).proj q = (s.proj q).addTerm t := rfl

theorem proj9_addAssertion_self (s : NDSt) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).proj q = (s.proj q).addAssertion x y := by
  simp [NDSt.proj, NDSt.addAssertion, NSt.addAssertion]

theorem proj9_addAssertion_other (s : NDSt) {q q' : Rel} (h : q' ≠ q) (x y : ℕ) :
    (s.addAssertion q x y).proj q' = s.proj q' := by
  simp [NDSt.proj, NDSt.addAssertion, Function.update_of_ne h]

theorem proj9_remove_self (s : NDSt) (q : Rel) (x y : ℕ) :
    (s.remove q x y).proj q = (s.proj q).remove x y := by
  simp [NDSt.proj, NDSt.remove, NSt.remove]

theorem proj9_remove_other (s : NDSt) {q q' : Rel} (h : q' ≠ q) (x y : ℕ) :
    (s.remove q x y).proj q' = s.proj q' := by
  simp [NDSt.proj, NDSt.remove, Function.update_of_ne h]

theorem proj9_identify (s : NDSt) (u v : ℕ) (q : Rel) :
    (s.identify u v).proj q = (s.proj q).identify u v := rfl

theorem addAssertion9_T (s : NDSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).T = s.T := rfl
theorem remove9_T (s : NDSt) (q : Rel) (x y : ℕ) : (s.remove q x y).T = s.T := rfl
theorem identify9_T (s : NDSt) (u v : ℕ) : (s.identify u v).T = s.T.erase v := rfl
theorem addTerm9_T (s : NDSt) (t : ℕ) : (s.addTerm t).T = insert t s.T := rfl

theorem wf_proj9 {s : NDSt} (hw : s.WF) (q : Rel) : (s.proj q).WF := by
  cases q
  · exact hw.1
  · exact hw.2

/-! ## The naming and forgetting maps -/

@[simp] theorem name9_T (s : NDSt) (c : ℕ) : (s.name c).T = s.T := rfl
@[simp] theorem name9_M (s : NDSt) (c : ℕ) : (s.name c).M = s.M := rfl
@[simp] theorem name9_a (s : NDSt) (c : ℕ) : (s.name c).a = c := rfl
@[simp] theorem name9_b (s : NDSt) (c : ℕ) : (s.name c).b = c := rfl
@[simp] theorem forget9_T (s : DSt) : s.forget.T = s.T := rfl
@[simp] theorem forget9_M (s : DSt) : s.forget.M = s.M := rfl

/-- Forgetting the names after naming gives the state back. -/
theorem forget_name9 (s : NDSt) (c : ℕ) : (s.name c).forget = s := rfl

/-- The names of a named state are one term. -/
theorem name9_names_one_term (s : NDSt) (c : ℕ) : (s.name c).a = (s.name c).b := rfl

/-- Naming then projecting is projecting then naming (the seventh's naming map on a part). -/
theorem proj_name9 (s : NDSt) (c : ℕ) (q : Rel) : (s.name c).proj q = (s.proj q).name c := rfl

theorem proj_forget9 (s : DSt) (q : Rel) : s.forget.proj q = (s.proj q).forget := rfl

theorem name9_addTerm (s : NDSt) (c t : ℕ) : (s.addTerm t).name c = (s.name c).addTerm t := rfl
theorem name9_addAssertion (s : NDSt) (c : ℕ) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).name c = (s.name c).addAssertion q x y := rfl
theorem name9_remove (s : NDSt) (c : ℕ) (q : Rel) (x y : ℕ) :
    (s.remove q x y).name c = (s.name c).remove q x y := rfl
theorem name9_identify (s : NDSt) (c u v : ℕ) :
    (s.identify u v).name (merge u v c) = (s.name c).identify u v := rfl

theorem forget9_addTerm (s : DSt) (t : ℕ) : (s.addTerm t).forget = s.forget.addTerm t := rfl
theorem forget9_addAssertion (s : DSt) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).forget = s.forget.addAssertion q x y := rfl
theorem forget9_remove (s : DSt) (q : Rel) (x y : ℕ) :
    (s.remove q x y).forget = s.forget.remove q x y := rfl
theorem forget9_identify (s : DSt) (u v : ℕ) : (s.identify u v).forget = s.forget.identify u v := rfl

theorem size_name9 (s : NDSt) (c : ℕ) : (s.name c).size = s.size := rfl
theorem size_forget9 (s : DSt) : s.forget.size = s.size := rfl

/-- A named state is well formed exactly when the state is and the names are on a term. -/
theorem name9_wf {s : NDSt} (hw : s.WF) {c : ℕ} (hc : c ∈ s.T) : (s.name c).WF :=
  ⟨⟨hw.1, hc, hc⟩, ⟨hw.2, hc, hc⟩⟩

theorem wf_of_name9 {s : NDSt} {c : ℕ} (h : (s.name c).WF) : s.WF ∧ c ∈ s.T :=
  ⟨⟨h.1.1, h.2.1⟩, h.1.2.1⟩

theorem wf_forget9 {s : DSt} (hw : s.WF) : s.forget.WF := ⟨hw.1.1, hw.2.1⟩

/-! ## The embedding of the seventh's states -/

theorem proj_ofR9_false (m : NSt) : m.ofR.proj false = m := rfl

theorem proj_ofR9_true (m : NSt) : m.ofR.proj true = ⟨m.T, fun _ => 0⟩ := rfl

theorem ofR9_T (m : NSt) : m.ofR.T = m.T := rfl

theorem ofR9_nothing_in_s (m : NSt) : m.ofR.NothingIn true := fun _ => rfl

theorem ofR9_wf {m : NSt} (hw : m.WF) : m.ofR.WF := ⟨hw, fun _ h => absurd rfl h⟩

theorem ofR9_addTerm (m : NSt) (t : ℕ) : (m.addTerm t).ofR = m.ofR.addTerm t := rfl

theorem ofR9_addAssertion (m : NSt) (x y : ℕ) :
    (m.addAssertion x y).ofR = m.ofR.addAssertion false x y := by
  apply ext_proj9
  intro q
  cases q
  · rw [proj9_addAssertion_self]
    rfl
  · rw [proj9_addAssertion_other _ (by decide)]
    rfl

theorem ofR9_remove (m : NSt) (x y : ℕ) : (m.remove x y).ofR = m.ofR.remove false x y := by
  apply ext_proj9
  intro q
  cases q
  · rw [proj9_remove_self]
    rfl
  · rw [proj9_remove_other _ (by decide)]
    rfl

/-- An empty relation stays empty under an identification. -/
theorem identify_zero9 (T : Finset ℕ) (u v : ℕ) :
    (⟨T, fun _ => 0⟩ : NSt).identify u v = ⟨T.erase v, fun _ => 0⟩ := by
  apply NSt.ext
  · rfl
  · funext p
    simp [NSt.identify]

theorem ofR9_identify (m : NSt) (u v : ℕ) : (m.identify u v).ofR = m.ofR.identify u v := by
  apply ext_proj9
  intro q
  cases q
  · rfl
  · show (⟨(m.identify u v).T, fun _ => 0⟩ : NSt) = (⟨m.T, fun _ => 0⟩ : NSt).identify u v
    rw [identify_zero9]
    rfl

/-- A state asserting nothing with `s` is the embedding of its `r` part. -/
theorem eq_ofR9_of_nothing_in_s {s : NDSt} (h : s.NothingIn true) : s = (s.proj false).ofR := by
  apply ext_proj9
  intro q
  cases q
  · rfl
  · apply NSt.ext
    · rfl
    · funext p
      exact h p

/-- The seventh's empty state, embedded, is the ninth's. -/
theorem ofR9_empty : Seed.Seventh.empty.ofR = empty9 := by
  apply ext_proj9
  intro q
  cases q <;> rfl

/-! ## The exchange of the two relations -/

theorem swap9_T (s : NDSt) : s.swap.T = s.T := rfl

theorem proj9_swap (s : NDSt) (q : Rel) : s.swap.proj q = s.proj (!q) := rfl

theorem swap9_swap (s : NDSt) : s.swap.swap = s := by
  apply NDSt.ext
  · rfl
  · funext q
    cases q <;> rfl

theorem swap9_addTerm (s : NDSt) (t : ℕ) : (s.addTerm t).swap = s.swap.addTerm t := rfl

theorem swap9_addAssertion (s : NDSt) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).swap = s.swap.addAssertion (!q) x y := by
  apply NDSt.ext
  · rfl
  · funext q' p
    cases q <;> cases q' <;> simp [NDSt.swap, NDSt.addAssertion, Function.update_apply]

theorem swap9_remove (s : NDSt) (q : Rel) (x y : ℕ) :
    (s.remove q x y).swap = s.swap.remove (!q) x y := by
  apply NDSt.ext
  · rfl
  · funext q' p
    cases q <;> cases q' <;> simp [NDSt.swap, NDSt.remove, Function.update_apply]

theorem swap9_identify (s : NDSt) (u v : ℕ) : (s.identify u v).swap = s.swap.identify u v := rfl

theorem swap9_empty : empty9.swap = empty9 := rfl

theorem swap9_wf {s : NDSt} (hw : s.WF) : s.swap.WF := ⟨hw.2, hw.1⟩

theorem swap9_M (s : NDSt) (q : Rel) : s.swap.M q = s.M (!q) := rfl

/-! ## The empty state -/

@[simp] theorem empty9_T : empty9.T = ∅ := rfl
@[simp] theorem empty9_M (q : Rel) (p : ℕ × ℕ) : empty9.M q p = 0 := rfl

theorem empty9_proj (q : Rel) : empty9.proj q = Seed.Seventh.empty := rfl

theorem empty9_wf : empty9.WF := ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩

theorem empty9_size : empty9.size = 0 := by
  show Seed.Seventh.empty.size + Seed.Seventh.empty.total = 0
  rw [Seed.Seventh.empty_size, Seed.Seventh.empty_total]

theorem empty9_not_nonempty : ¬ empty9.T.Nonempty := by simp [empty9]

/-- A well-formed state without terms is the empty state. -/
theorem eq_empty9_of_wf {s : NDSt} (hw : s.WF) (h : ¬ s.T.Nonempty) : s = empty9 := by
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply NDSt.ext
  · exact h
  · funext q p
    by_contra hp
    have hx : p.1 ∈ s.T := ((wf_proj9 hw q) p hp).1
    rw [h] at hx
    exact absurd hx (Finset.notMem_empty _)

/-! ## Size -/

/-- The size is the terms once plus both totals: the seventh's size of the `r` part plus the
`s` total. -/
theorem size9_eq (s : NDSt) : s.size = s.T.card + (s.proj false).total + (s.proj true).total := by
  unfold NDSt.size NSt.size
  rfl

theorem size9_swap (s : NDSt) : s.swap.size = s.size := by
  rw [size9_eq, size9_eq]
  show s.T.card + (s.proj true).total + (s.proj false).total = _
  omega

theorem total_zero9 (T : Finset ℕ) : (⟨T, fun _ => 0⟩ : NSt).total = 0 := by simp [NSt.total]

theorem size_addTerm9 {s : NDSt} (hw : s.WF) {t : ℕ} (ht : t ∉ s.T) :
    (s.addTerm t).size = s.size + 1 := by
  unfold NDSt.size
  rw [proj9_addTerm, proj9_addTerm, Seed.Seventh.size_addTerm7 hw.1 ht, Seed.Seventh.total_addTerm7 hw.2]
  omega

theorem addTerm9_wf {s : NDSt} (hw : s.WF) (t : ℕ) : (s.addTerm t).WF :=
  ⟨Seed.Seventh.addTerm_wf hw.1 t, Seed.Seventh.addTerm_wf hw.2 t⟩

/-- Adding an assertion of either relation raises the size by one (the fourth's lemma on the
part through the naming map). -/
theorem size_addAssertion9 {s : NDSt} (q : Rel) {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) :
    (s.addAssertion q x y).size = s.size + 1 := by
  have e : ((s.proj q).addAssertion x y).total = (s.proj q).total + 1 :=
    Seed.Fourth.total_addAssertion (s := (s.proj q).name x) hx hy
  cases q
  · rw [size9_eq, size9_eq, addAssertion9_T, proj9_addAssertion_self, proj9_addAssertion_other s (by decide) x y]
    omega
  · rw [size9_eq, size9_eq, addAssertion9_T, proj9_addAssertion_self, proj9_addAssertion_other s (by decide) x y]
    omega

/-- Removing an assertion of either relation lowers the size by one (the fifth's lemma on the
part through the naming map). -/
theorem size_remove9 {s : NDSt} (hw : s.WF) (q : Rel) {x y : ℕ} (hp : s.M q (x, y) ≠ 0) :
    (s.remove q x y).size + 1 = s.size := by
  have hx : x ∈ s.T := ((wf_proj9 hw q) (x, y) hp).1
  have hy : y ∈ s.T := ((wf_proj9 hw q) (x, y) hp).2
  have e : ((s.proj q).remove x y).size + 1 = (s.proj q).size :=
    Seed.Fifth.size_remove ((s.proj q).name x) hx hy hp
  have hT : ((s.proj q).remove x y).T.card = (s.proj q).T.card := rfl
  unfold NSt.size at e
  cases q
  · rw [size9_eq, size9_eq, remove9_T, proj9_remove_self, proj9_remove_other s (by decide) x y]
    omega
  · rw [size9_eq, size9_eq, remove9_T, proj9_remove_self, proj9_remove_other s (by decide) x y]
    omega

/-- Identifying two terms lowers the size by one: both totals are kept (the fifth's lemma on
each part) and the terms lose one. -/
theorem size_identify9 {s : NDSt} {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
    (s.identify u v).size + 1 = s.size := by
  have e0 : ((s.identify u v).proj false).total = (s.proj false).total :=
    Seed.Fifth.total_identify ((s.proj false).name u) hu huv
  have e1 : ((s.identify u v).proj true).total = (s.proj true).total :=
    Seed.Fifth.total_identify ((s.proj true).name u) hu huv
  have hc : (s.T.erase v).card + 1 = s.T.card := Finset.card_erase_add_one hv
  rw [size9_eq, size9_eq, identify9_T, e0, e1]
  omega

/-- The one-term state: a term added to the empty state. -/
def oneTerm9 : NDSt := empty9.addTerm 0

theorem size_oneTerm9 (t : ℕ) : (empty9.addTerm t).size = 1 := by
  rw [size_addTerm9 empty9_wf (by simp [empty9]), empty9_size]

theorem oneTerm9_wf : oneTerm9.WF := addTerm9_wf empty9_wf 0

theorem mem_oneTerm9_T (x : ℕ) : x ∈ oneTerm9.T ↔ x = 0 := by simp [oneTerm9, NDSt.addTerm, empty9]

theorem oneTerm9_proj (q : Rel) : oneTerm9.proj q = oneTerm7 := rfl

end Seed.Ninth
