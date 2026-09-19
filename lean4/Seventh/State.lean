import Sixth.Rename

/-!
# The seventh seed: nothing is given

`prompt/seventh/seed_prompt.md` is the sixth seed with its given replaced by
"Nothing is given: to begin with there are no terms and nothing is asserted."
There is no `a`, no `b`, and the beginning has no terms.  The sixth's `MSt`
carries the two names as fields and its `WF` puts them among the terms, so a
state without terms is not well formed there: the seventh seed needs a state
without names.

* `NSt`: terms and a multiplicity for each ordered pair.  `WF`, `total`, `size`
  and the four operations are the sixth's definitions with the names left out.
* `empty`: the beginning.
* Two maps connect the two models, both needed to cite the sixth's results and
  to say whether they survive without the given and the names:
  - `MSt.forget`: a sixth state with its names dropped;
  - `NSt.name s c`: a seventh state with both names put on the term `c`, well
    formed exactly when `c` is a term (`name_wf`, `wf_of_name`).
  Forgetting after naming gives the state back (`forget_name`), the operations
  commute with both maps definitionally (`name_addTerm`, …, `forget_identify`),
  and the size is the same on both sides (`size_name`, `size_forget`).

Derived here: the empty state is well formed and has size 0; a well-formed
state without terms is the empty state (`eq_empty_of_wf`); adding a term to a
well-formed state raises its size by one (`size_addTerm7`, the fourth's
`size_addTerm` re-proved without names, since on the empty state no naming is
possible).
-/

namespace Seed.Seventh

open Seed Seed.Fourth Seed.Fifth Seed.Sixth

/-- A state of the seventh seed: terms and a multiplicity for each ordered pair.  No names. -/
@[ext]
structure NSt where
  T : Finset ℕ
  M : ℕ × ℕ → ℕ

namespace NSt

/-- Only pairs of terms that are there have a positive multiplicity. -/
def WF (s : NSt) : Prop := ∀ p, s.M p ≠ 0 → p.1 ∈ s.T ∧ p.2 ∈ s.T

/-- No `xrx` is asserted (a property a state may have, as under the sixth seed). -/
def Legal (s : NSt) : Prop := ∀ x, s.M (x, x) = 0

/-- Adding a term. -/
def addTerm (s : NSt) (t : ℕ) : NSt := ⟨insert t s.T, s.M⟩

/-- Adding an assertion: its multiplicity rises by one. -/
def addAssertion (s : NSt) (x y : ℕ) : NSt := ⟨s.T, Function.update s.M (x, y) (s.M (x, y) + 1)⟩

/-- Removing an assertion: its multiplicity falls by one. -/
def remove (s : NSt) (x y : ℕ) : NSt := ⟨s.T, Function.update s.M (x, y) (s.M (x, y) - 1)⟩

/-- Identifying `u` and `v`: both are replaced by one term (written `u`) in every assertion;
the multiplicities of the pairs that become one pair add up (the fifth's reading). -/
def identify (s : NSt) (u v : ℕ) : NSt :=
  ⟨s.T.erase v, fun p => ∑ q ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = p), s.M q⟩

/-- The sum of the multiplicities over the pairs of terms. -/
def total (s : NSt) : ℕ := ∑ p ∈ s.T ×ˢ s.T, s.M p

/-- Terms plus assertions, counted with multiplicity. -/
def size (s : NSt) : ℕ := s.T.card + s.total

/-- The state read as a state of the sixth seed, both names on the term `c`. -/
def name (s : NSt) (c : ℕ) : MSt := ⟨s.T, s.M, c, c⟩

end NSt

open NSt

/-- What is given: no terms, nothing asserted. -/
def empty : NSt := ⟨∅, fun _ => 0⟩

/-- A state of the sixth seed with its names forgotten. -/
def _root_.Seed.Fourth.MSt.forget (s : MSt) : NSt := ⟨s.T, s.M⟩

/-! ## The two maps -/

@[simp] theorem name_T (s : NSt) (c : ℕ) : (s.name c).T = s.T := rfl
@[simp] theorem name_M (s : NSt) (c : ℕ) : (s.name c).M = s.M := rfl
@[simp] theorem name_a (s : NSt) (c : ℕ) : (s.name c).a = c := rfl
@[simp] theorem name_b (s : NSt) (c : ℕ) : (s.name c).b = c := rfl
@[simp] theorem forget_T (s : MSt) : s.forget.T = s.T := rfl
@[simp] theorem forget_M (s : MSt) : s.forget.M = s.M := rfl

/-- Forgetting the names after naming gives the state back. -/
theorem forget_name (s : NSt) (c : ℕ) : (s.name c).forget = s := rfl

/-- The names of a named state are one term. -/
theorem name_names_one_term (s : NSt) (c : ℕ) : (s.name c).a = (s.name c).b := rfl

theorem name_addTerm (s : NSt) (c t : ℕ) : (s.addTerm t).name c = (s.name c).addTerm t := rfl
theorem name_addAssertion (s : NSt) (c x y : ℕ) :
    (s.addAssertion x y).name c = (s.name c).addAssertion x y := rfl
theorem name_remove (s : NSt) (c x y : ℕ) : (s.remove x y).name c = (s.name c).remove x y := rfl
theorem name_identify (s : NSt) (c u v : ℕ) :
    (s.identify u v).name (merge u v c) = (s.name c).identify u v := rfl

theorem forget_addTerm (s : MSt) (t : ℕ) : (s.addTerm t).forget = s.forget.addTerm t := rfl
theorem forget_addAssertion (s : MSt) (x y : ℕ) :
    (s.addAssertion x y).forget = s.forget.addAssertion x y := rfl
theorem forget_remove (s : MSt) (x y : ℕ) : (s.remove x y).forget = s.forget.remove x y := rfl
theorem forget_identify (s : MSt) (u v : ℕ) : (s.identify u v).forget = s.forget.identify u v := rfl

theorem total_name (s : NSt) (c : ℕ) : (s.name c).total = s.total := rfl
theorem size_name (s : NSt) (c : ℕ) : (s.name c).size = s.size := rfl
theorem total_forget (s : MSt) : s.forget.total = s.total := rfl
theorem size_forget (s : MSt) : s.forget.size = s.size := rfl

/-- A named state is well formed exactly when the state is and the names are on a term. -/
theorem name_wf {s : NSt} (hw : s.WF) {c : ℕ} (hc : c ∈ s.T) : (s.name c).WF := ⟨hw, hc, hc⟩

theorem wf_of_name {s : NSt} {c : ℕ} (h : (s.name c).WF) : s.WF ∧ c ∈ s.T := ⟨h.1, h.2.1⟩

theorem wf_forget {s : MSt} (hw : s.WF) : s.forget.WF := hw.1

theorem legal_name_iff (s : NSt) (c : ℕ) : (s.name c).Legal ↔ s.Legal := Iff.rfl

/-! ## The empty state -/

@[simp] theorem empty_T : empty.T = ∅ := rfl
@[simp] theorem empty_M (p : ℕ × ℕ) : empty.M p = 0 := rfl

theorem empty_wf : empty.WF := fun _ h => absurd rfl h

theorem empty_total : empty.total = 0 := by simp [NSt.total, empty]

theorem empty_size : empty.size = 0 := by
  unfold NSt.size
  rw [empty_total, empty_T, Finset.card_empty]

theorem empty_not_nonempty : ¬ empty.T.Nonempty := by simp [empty]

/-- A well-formed state without terms is the empty state. -/
theorem eq_empty_of_wf {s : NSt} (hw : s.WF) (h : ¬ s.T.Nonempty) : s = empty := by
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply NSt.ext
  · exact h
  · funext p
    by_contra hp
    have := (hw p hp).1
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)

/-! ## Adding a term raises the size by one (no naming possible on the empty state) -/

theorem total_addTerm7 {s : NSt} (hw : s.WF) (t : ℕ) : (s.addTerm t).total = s.total := by
  unfold NSt.total NSt.addTerm
  symm
  apply Finset.sum_subset
  · exact Finset.product_subset_product (Finset.subset_insert _ _) (Finset.subset_insert _ _)
  · intro p _ hp
    by_contra h
    exact hp (Finset.mem_product.2 (hw p h))

theorem size_addTerm7 {s : NSt} (hw : s.WF) {t : ℕ} (ht : t ∉ s.T) :
    (s.addTerm t).size = s.size + 1 := by
  unfold NSt.size
  rw [total_addTerm7 hw]
  show (insert t s.T).card + s.total = s.T.card + s.total + 1
  rw [Finset.card_insert_of_notMem ht]
  omega

theorem addTerm_wf {s : NSt} (hw : s.WF) (t : ℕ) : (s.addTerm t).WF := by
  intro p hp
  exact ⟨Finset.mem_insert_of_mem (hw p hp).1, Finset.mem_insert_of_mem (hw p hp).2⟩

/-- The one-term state: a term added to the empty state. -/
theorem size_oneTerm7 (t : ℕ) : (empty.addTerm t).size = 1 := by
  rw [size_addTerm7 empty_wf (by simp [empty]), empty_size]

end Seed.Seventh
