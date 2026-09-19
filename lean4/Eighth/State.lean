import Seventh.Rename

/-!
# The eighth seed: two relations

`prompt/eighth/seed_prompt.md` is the sixth seed with a second relation: an
assertion is `xry` or `xsy`, `r` and `s` being the two relations between the
same terms; `arb` alone is given, and `s` begins used by nothing.

* `Rel`: a relation tag, `false` for `r` and `true` for `s`.
* `DSt`: terms, a multiplicity function for each relation, and the names.
* `DSt.proj q`: the `r` part or the `s` part — a state of the sixth seed with
  the same terms and names.  Well-formedness is well-formedness of both parts;
  the size counts the terms once and both totals.
* `MSt.ofR`: a state of the sixth seed read as a two-relation state asserting
  nothing with `s`.  Its `r` part is the state itself (`proj_ofR_false`, by
  the eta rule of structures).
* The four operations: a term and an identification act on both relations;
  an assertion and a removal act on one.  Each commutes with the projections
  (`proj_addTerm`, `proj_addAssertion_self`, `proj_addAssertion_other`, …,
  `proj_identify`), which is how the sixth's lemmas on one multiplicity
  function are cited: on a part.

Derived here: the two beginnings are well formed; a two-relation state is
determined by its two parts (`ext_proj`); an empty relation stays empty under
an identification (`identify_zero`), so the sixth's changes lift to the states
asserting nothing with `s` (`ofR_addTerm`, `ofR_addAssertion`, `ofR_remove`,
`ofR_identify`).
-/

namespace Seed.Eighth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth

/-- A relation tag: `false` is `r`, `true` is `s`. -/
abbrev Rel := Bool

/-- Terms, a multiplicity for each ordered pair in each relation, and the terms named `a`, `b`. -/
@[ext]
structure DSt where
  T : Finset ℕ
  M : Rel → ℕ × ℕ → ℕ
  a : ℕ
  b : ℕ

namespace DSt

/-- The `r` part (`q = false`) or the `s` part (`q = true`): a state of the sixth seed. -/
def proj (s : DSt) (q : Rel) : MSt := ⟨s.T, s.M q, s.a, s.b⟩

/-- Both parts are well formed (they share the terms and the names). -/
def WF (s : DSt) : Prop := (s.proj false).WF ∧ (s.proj true).WF

/-- Nothing is asserted with `s`. -/
def NothingInS (s : DSt) : Prop := ∀ p, s.M true p = 0

/-- Adding a term (to both relations at once, since they share the terms). -/
def addTerm (s : DSt) (t : ℕ) : DSt := ⟨insert t s.T, s.M, s.a, s.b⟩

/-- Adding an assertion of relation `q`: its multiplicity rises by one. -/
def addAssertion (s : DSt) (q : Rel) (x y : ℕ) : DSt :=
  ⟨s.T, Function.update s.M q (Function.update (s.M q) (x, y) (s.M q (x, y) + 1)), s.a, s.b⟩

/-- Removing an assertion of relation `q`: its multiplicity falls by one. -/
def remove (s : DSt) (q : Rel) (x y : ℕ) : DSt :=
  ⟨s.T, Function.update s.M q (Function.update (s.M q) (x, y) (s.M q (x, y) - 1)), s.a, s.b⟩

/-- Identifying `u` and `v` in every assertion of both relations; the multiplicities of the
pairs that become one pair add up, in each relation separately. -/
def identify (s : DSt) (u v : ℕ) : DSt :=
  ⟨s.T.erase v,
    fun q p => ∑ w ∈ (s.T ×ˢ s.T).filter (fun w => (merge u v w.1, merge u v w.2) = p), s.M q w,
    merge u v s.a, merge u v s.b⟩

/-- Terms plus the assertions of both relations, counted with multiplicity. -/
def size (s : DSt) : ℕ := (s.proj false).size + (s.proj true).total

end DSt

open DSt

/-- A state of the sixth seed read as a two-relation state asserting nothing with `s`. -/
def _root_.Seed.Fourth.MSt.ofR (m : MSt) : DSt :=
  ⟨m.T, fun q => match q with
    | false => m.M
    | true => fun _ => 0, m.a, m.b⟩

/-! ## Projections -/

@[simp] theorem proj_T (s : DSt) (q : Rel) : (s.proj q).T = s.T := rfl
@[simp] theorem proj_M (s : DSt) (q : Rel) : (s.proj q).M = s.M q := rfl
@[simp] theorem proj_a (s : DSt) (q : Rel) : (s.proj q).a = s.a := rfl
@[simp] theorem proj_b (s : DSt) (q : Rel) : (s.proj q).b = s.b := rfl

/-- A two-relation state is determined by its two parts. -/
theorem ext_proj {s t : DSt} (h : ∀ q, s.proj q = t.proj q) : s = t := by
  apply DSt.ext
  · exact congrArg MSt.T (h false)
  · funext q
    exact congrArg MSt.M (h q)
  · exact congrArg MSt.a (h false)
  · exact congrArg MSt.b (h false)

theorem proj_addTerm (s : DSt) (t : ℕ) (q : Rel) : (s.addTerm t).proj q = (s.proj q).addTerm t := rfl

theorem proj_addAssertion_self (s : DSt) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).proj q = (s.proj q).addAssertion x y := by
  simp [DSt.proj, DSt.addAssertion, MSt.addAssertion]

theorem proj_addAssertion_other (s : DSt) {q q' : Rel} (h : q' ≠ q) (x y : ℕ) :
    (s.addAssertion q x y).proj q' = s.proj q' := by
  simp [DSt.proj, DSt.addAssertion, Function.update_of_ne h]

theorem proj_remove_self (s : DSt) (q : Rel) (x y : ℕ) :
    (s.remove q x y).proj q = (s.proj q).remove x y := by
  simp [DSt.proj, DSt.remove, MSt.remove]

theorem proj_remove_other (s : DSt) {q q' : Rel} (h : q' ≠ q) (x y : ℕ) :
    (s.remove q x y).proj q' = s.proj q' := by
  simp [DSt.proj, DSt.remove, Function.update_of_ne h]

theorem proj_identify (s : DSt) (u v : ℕ) (q : Rel) :
    (s.identify u v).proj q = (s.proj q).identify u v := rfl

theorem addAssertion_T (s : DSt) (q : Rel) (x y : ℕ) : (s.addAssertion q x y).T = s.T := rfl
theorem remove_T (s : DSt) (q : Rel) (x y : ℕ) : (s.remove q x y).T = s.T := rfl
theorem identify_T (s : DSt) (u v : ℕ) : (s.identify u v).T = s.T.erase v := rfl
theorem addTerm_T (s : DSt) (t : ℕ) : (s.addTerm t).T = insert t s.T := rfl
theorem identify_a (s : DSt) (u v : ℕ) : (s.identify u v).a = merge u v s.a := rfl
theorem identify_b (s : DSt) (u v : ℕ) : (s.identify u v).b = merge u v s.b := rfl

/-- The other relation, and that the two tags differ. -/
theorem not_ne (q : Rel) : (!q) ≠ q := by cases q <;> decide

/-! ## The embedding of the sixth's states -/

theorem proj_ofR_false (m : MSt) : m.ofR.proj false = m := rfl

theorem proj_ofR_true (m : MSt) : m.ofR.proj true = ⟨m.T, fun _ => 0, m.a, m.b⟩ := rfl

theorem ofR_T (m : MSt) : m.ofR.T = m.T := rfl

theorem ofR_nothing_in_s (m : MSt) : m.ofR.NothingInS := fun _ => rfl

theorem ofR_wf {m : MSt} (hw : m.WF) : m.ofR.WF :=
  ⟨hw, ⟨fun _ h => absurd rfl h, hw.2.1, hw.2.2⟩⟩

theorem ofR_addTerm (m : MSt) (t : ℕ) : (m.addTerm t).ofR = m.ofR.addTerm t := rfl

theorem ofR_addAssertion (m : MSt) (x y : ℕ) : (m.addAssertion x y).ofR = m.ofR.addAssertion false x y := by
  apply ext_proj
  intro q
  cases q
  · rw [proj_addAssertion_self]
    rfl
  · rw [proj_addAssertion_other _ (by decide)]
    rfl

theorem ofR_remove (m : MSt) (x y : ℕ) : (m.remove x y).ofR = m.ofR.remove false x y := by
  apply ext_proj
  intro q
  cases q
  · rw [proj_remove_self]
    rfl
  · rw [proj_remove_other _ (by decide)]
    rfl

/-- An empty relation stays empty under an identification. -/
theorem identify_zero (T : Finset ℕ) (a b u v : ℕ) :
    (⟨T, fun _ => 0, a, b⟩ : MSt).identify u v = ⟨T.erase v, fun _ => 0, merge u v a, merge u v b⟩ := by
  apply MSt.ext
  · rfl
  · funext p
    simp [MSt.identify]
  · rfl
  · rfl

theorem ofR_identify (m : MSt) (u v : ℕ) : (m.identify u v).ofR = m.ofR.identify u v := by
  apply ext_proj
  intro q
  cases q
  · rfl
  · show (⟨(m.identify u v).T, fun _ => 0, (m.identify u v).a, (m.identify u v).b⟩ : MSt) =
      (⟨m.T, fun _ => 0, m.a, m.b⟩ : MSt).identify u v
    rw [identify_zero]
    rfl

/-- A state asserting nothing with `s` is the embedding of its `r` part. -/
theorem eq_ofR_of_nothing_in_s {s : DSt} (h : s.NothingInS) : s = (s.proj false).ofR := by
  apply ext_proj
  intro q
  cases q
  · rfl
  · apply MSt.ext
    · rfl
    · funext p
      exact h p
    · rfl
    · rfl

/-! ## Size and well-formedness -/

theorem size_eq (s : DSt) : s.size = s.T.card + (s.proj false).total + (s.proj true).total := by
  unfold DSt.size MSt.size
  rfl

theorem size_ofR (m : MSt) : m.ofR.size = m.size := by
  rw [size_eq, proj_ofR_false, proj_ofR_true]
  unfold MSt.size MSt.total
  simp [ofR_T]

theorem wf_proj {s : DSt} (hw : s.WF) (q : Rel) : (s.proj q).WF := by
  cases q
  · exact hw.1
  · exact hw.2

/-! ## What is given -/

/-- What is given, `bra` not asserted: `arb` once, nothing with `s`. -/
def givenA8 : DSt := givenA4.ofR

/-- What is given, `bra` asserted: `arb` and `bra` once, nothing with `s`. -/
def givenB8 : DSt := givenB4.ofR

theorem givenA8_wf : givenA8.WF := ofR_wf givenA4_wf
theorem givenB8_wf : givenB8.WF := ofR_wf givenB4_wf
theorem givenA8_proj : givenA8.proj false = givenA4 := rfl
theorem givenB8_proj : givenB8.proj false = givenB4 := rfl
theorem givenA8_a : givenA8.a = 0 := rfl
theorem givenA8_b : givenA8.b = 1 := rfl
theorem givenB8_a : givenB8.a = 0 := rfl
theorem givenB8_b : givenB8.b = 1 := rfl
theorem givenA8_nonempty : givenA8.T.Nonempty := ⟨0, (mem_givenA4_T 0).2 (Or.inl rfl)⟩

theorem size_givenA8 : givenA8.size = 3 := by rw [givenA8, size_ofR, size_givenA4]
theorem size_givenB8 : givenB8.size = 4 := by rw [givenB8, size_ofR, size_givenB4]

end Seed.Eighth
