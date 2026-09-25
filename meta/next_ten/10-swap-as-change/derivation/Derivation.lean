/-!
# Problem 10 (swap-as-change) Formal Derivation

Seed edit from Ninth seed:
"A change is exactly one of: identifying two terms; removing an assertion;
adding a term; adding an assertion; exchanging the relations. Nothing else is a
change. Identifying two terms replaces both by one term in every assertion.
Exchanging the relations replaces every `xry` with `xsy` and every `xsy` with
`xry`, preserving each multiplicity."

Formalized here for aggregate states recording a term count and total multiplicity
in each relation. Individual term pairs and their assertion multiplicities are
handled in the paper model and Python checks, not in this Lean model.

Results in the aggregate model:
1. `swap` involution: `s.swap.swap = s`.
2. `swap` preserves size and well-formedness: `s.swap.size = s.size`, `s.swap.WF`.
3. `Step10`: the five kinds of change (the four kinds of Step9, plus swap).
4. Invariants of one change:
   - Well-formedness is preserved (`Step10.wf`).
   - Size increases by at most one (`Step10.size_le`).
5. Sequences of changes (`Reach10 s t n`).
6. Cost bounds:
   - Size upper bound: `t.size ≤ s.size + n`.
   - Lower bound from empty: any sequence reaching `g` from `empty9` requires at least `g.size` changes.
   - Additions alone reach `g` from `empty9` in `g.size` changes.
   - The fewest changes from `empty9` to `g` is exactly `g.size` (identical to Ninth).
7. Cost reduction between states:
   - Single-step swap reachability: `Reach10 s s.swap 1` whenever `s.swap ≠ s`.
   - In Ninth, any sequence between `s` and `s.swap` (when different) has even length ≥ 2.
   - Therefore, swap strictly reduces the shortest path cost from `s` to `s.swap` from ≥ 2 to 1.
8. What does not follow:
   - It does not follow that swap reduces shortest cost from empty: `cost(empty9, g) = g.size` is unchanged.
   - It does not follow that Ninth shortest costs are preserved between arbitrary state pairs: asymmetric pairs have strictly shorter paths.

Self-contained: no external project module dependencies. Standard Lean 4 core only.
-/

set_option linter.unusedVariables false

namespace Seed.Problem10

abbrev ℕ := Nat

/-- Two relations: false = r, true = s. -/
abbrev Rel := Bool

/-- A two-relation aggregate state: term count `n`, total `r` assertions, total `s` assertions. -/
@[ext]
structure NDSt where
  n : Nat
  r : Nat
  s : Nat
deriving DecidableEq, Repr

abbrev DState := NDSt

namespace NDSt

/-- Well-formedness: if there are no terms, there can be no assertions. -/
def WF (st : NDSt) : Prop :=
  st.n = 0 → st.r = 0 ∧ st.s = 0

/-- Exchanging the relations swaps their aggregate assertion counts. -/
def swap (st : NDSt) : NDSt :=
  ⟨st.n, st.s, st.r⟩

/-- Total size of a state: terms plus total assertion multiplicity across both relations. -/
def size (st : NDSt) : Nat :=
  st.n + st.r + st.s

/-- The empty state: 0 terms, 0 assertions in r, 0 assertions in s. -/
def empty9 : NDSt :=
  ⟨0, 0, 0⟩

def addTerm (st : NDSt) : NDSt :=
  ⟨st.n + 1, st.r, st.s⟩

def addAssertion (st : NDSt) (q : Rel) : NDSt :=
  match q with
  | false => ⟨st.n, st.r + 1, st.s⟩
  | true  => ⟨st.n, st.r, st.s + 1⟩

def removeAssertion (st : NDSt) (q : Rel) : NDSt :=
  match q with
  | false => ⟨st.n, st.r - 1, st.s⟩
  | true  => ⟨st.n, st.r, st.s - 1⟩

def identify (st : NDSt) : NDSt :=
  ⟨st.n - 1, st.r, st.s⟩

end NDSt

open NDSt

/-- What is given: no terms, nothing asserted in either relation. -/
def empty9 : NDSt := NDSt.empty9

theorem empty9_wf : empty9.WF := by
  intro h
  exact ⟨rfl, rfl⟩

theorem empty9_size : empty9.size = 0 := rfl

/-! ## Swap properties -/

/-- Swap is an involution: exchanging relations twice returns the original state. -/
theorem swap_involution (s : NDSt) : s.swap.swap = s := rfl

/-- Swap preserves the size of the state. -/
theorem swap_size (s : NDSt) : s.swap.size = s.size := by
  dsimp [size, swap]
  omega

/-- Swap preserves well-formedness. -/
theorem swap_wf {s : NDSt} (hw : s.WF) : s.swap.WF := by
  intro h
  have := hw h
  exact ⟨this.2, this.1⟩

/-- Swap on the empty state is the empty state. -/
theorem swap_empty : empty9.swap = empty9 := rfl

/-! ## Step Relations -/

/-- One change of the parent Ninth derivation: four kinds of change. -/
inductive Step9 : NDSt → NDSt → Prop where
  | addTerm (s : NDSt) :
      Step9 s ⟨s.n + 1, s.r, s.s⟩
  | addAssertionR (s : NDSt) (hn : s.n ≥ 1) :
      Step9 s ⟨s.n, s.r + 1, s.s⟩
  | addAssertionS (s : NDSt) (hn : s.n ≥ 1) :
      Step9 s ⟨s.n, s.r, s.s + 1⟩
  | removeR (s : NDSt) (hr : s.r ≥ 1) :
      Step9 s ⟨s.n, s.r - 1, s.s⟩
  | removeS (s : NDSt) (hs : s.s ≥ 1) :
      Step9 s ⟨s.n, s.r, s.s - 1⟩
  | identify (s : NDSt) (hn : s.n ≥ 2) :
      Step9 s ⟨s.n - 1, s.r, s.s⟩

/-- Step9 preserves well-formedness. -/
theorem Step9.wf {s t : NDSt} (h : Step9 s t) (hw : s.WF) : t.WF := by
  cases h with
  | addTerm =>
    intro h0; dsimp at h0; omega
  | addAssertionR hn =>
    intro h0; dsimp at h0; omega
  | addAssertionS hn =>
    intro h0; dsimp at h0; omega
  | removeR hr =>
    intro h0; dsimp at h0; have := hw h0; omega
  | removeS hs =>
    intro h0; dsimp at h0; have := hw h0; omega
  | identify hn =>
    intro h0; dsimp at h0; omega

/-- Every change of Step9 moves the size by exactly one (+1 or -1). -/
theorem Step9.size_step {s t : NDSt} (h : Step9 s t) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size := by
  cases h with
  | addTerm =>
    left; dsimp [size]; omega
  | addAssertionR hn =>
    left; dsimp [size]; omega
  | addAssertionS hn =>
    left; dsimp [size]; omega
  | removeR hr =>
    right; dsimp [size]; omega
  | removeS hs =>
    right; dsimp [size]; omega
  | identify hn =>
    right; dsimp [size]; omega

/-! ## The five kinds of change of Problem 10 -/

/-- One change of Problem 10: identifying two terms, removing an assertion,
adding a term, adding an assertion, or exchanging the relations.
Under the chosen reading, a swap counts as a change only when it changes the written state. -/
inductive Step10 : NDSt → NDSt → Prop where
  | ofStep9 {s t : NDSt} : Step9 s t → Step10 s t
  | swap (s : NDSt) (hdiff : s.swap ≠ s) : Step10 s s.swap

/-- Adding a term is a change of Problem 10. -/
theorem Step10.addTerm (s : NDSt) : Step10 s ⟨s.n + 1, s.r, s.s⟩ :=
  Step10.ofStep9 (Step9.addTerm s)

/-- Adding an assertion is a change of Problem 10. -/
theorem Step10.addAssertion (s : NDSt) (q : Rel) (hn : s.n ≥ 1) :
    Step10 s (s.addAssertion q) := by
  cases q with
  | false => exact Step10.ofStep9 (Step9.addAssertionR s hn)
  | true  => exact Step10.ofStep9 (Step9.addAssertionS s hn)

/-- Removing an assertion is a change of Problem 10. -/
theorem Step10.remove (s : NDSt) (q : Rel) (hq : match q with | false => s.r ≥ 1 | true => s.s ≥ 1) :
    Step10 s (s.removeAssertion q) := by
  cases q with
  | false => exact Step10.ofStep9 (Step9.removeR s hq)
  | true  => exact Step10.ofStep9 (Step9.removeS s hq)

/-- Identifying two terms is a change of Problem 10. -/
theorem Step10.identify (s : NDSt) (hn : s.n ≥ 2) :
    Step10 s ⟨s.n - 1, s.r, s.s⟩ :=
  Step10.ofStep9 (Step9.identify s hn)

/-! ## Invariants of one change -/

/-- Well-formedness is preserved by every change of Problem 10. -/
theorem Step10.wf {s t : NDSt} (h : Step10 s t) (hw : s.WF) : t.WF := by
  cases h with
  | ofStep9 st => exact st.wf hw
  | swap _ => exact swap_wf hw

/-- Every change of Problem 10 raises size by 1, lowers size by 1, or keeps size constant (swap). -/
theorem Step10.size_step {s t : NDSt} (h : Step10 s t) (hw : s.WF) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size ∨ t.size = s.size := by
  cases h with
  | ofStep9 st =>
    rcases st.size_step with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  | swap hdiff =>
    exact Or.inr (Or.inr (swap_size s))

/-- Every change of Problem 10 increases size by at most one. -/
theorem Step10.size_le {s t : NDSt} (h : Step10 s t) (hw : s.WF) : t.size ≤ s.size + 1 := by
  rcases h.size_step hw with e | e | e <;> omega

/-! ## Sequences of changes -/

/-- `Reach9 s t n`: `t` is reached from `s` by `n` changes of Ninth. -/
inductive Reach9 : NDSt → NDSt → Nat → Prop where
  | refl (s : NDSt) : Reach9 s s 0
  | step {s t u : NDSt} {n : Nat} : Reach9 s t n → Step9 t u → Reach9 s u (n + 1)

/-- `Reach10 s t n`: `t` is reached from `s` by `n` changes of Problem 10. -/
inductive Reach10 : NDSt → NDSt → Nat → Prop where
  | refl (s : NDSt) : Reach10 s s 0
  | step {s t u : NDSt} {n : Nat} : Reach10 s t n → Step10 t u → Reach10 s u (n + 1)

/-- Every sequence of Ninth changes is a sequence of Problem 10 changes. -/
theorem Reach9.toReach10 {s t : NDSt} {n : Nat} (h : Reach9 s t n) :
    Reach10 s t n := by
  induction h with
  | refl => exact Reach10.refl _
  | step _ st ih => exact Reach10.step ih (Step10.ofStep9 st)

/-- Transitivity of reachability in Reach9. -/
theorem Reach9.trans {s t u : NDSt} {n m : Nat} (h1 : Reach9 s t n) (h2 : Reach9 t u m) :
    Reach9 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach9.step ih st

/-- Transitivity of reachability in Reach10. -/
theorem Reach10.trans {s t u : NDSt} {n m : Nat} (h1 : Reach10 s t n) (h2 : Reach10 t u m) :
    Reach10 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach10.step ih st

/-- Well-formedness is preserved by any sequence of changes. -/
theorem Reach10.wf {s t : NDSt} {n : Nat} (h : Reach10 s t n) (hw : s.WF) : t.WF := by
  induction h with
  | refl => exact hw
  | step _ st ih => exact st.wf ih

/-- Upper bound on size: a state reached in `n` changes from `s` has size at most `s.size + n`. -/
theorem Reach10.size_le {s t : NDSt} {n : Nat} (h : Reach10 s t n) (hw : s.WF) :
    t.size ≤ s.size + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have hw_mid := r.wf hw
    have hstep := st.size_le hw_mid
    omega

/-! ## Fewest changes from empty -/

/-- **Lower bound from empty.** A state reached from `empty9` in `n` changes has size at most `n`. -/
theorem fewest_changes10_lower {g : NDSt} {n : Nat} (h : Reach10 empty9 g n) : g.size ≤ n := by
  have hle := h.size_le empty9_wf
  rw [empty9_size] at hle
  omega

/-- Adding terms one by one from empty. -/
theorem reach9_addTerms (k : Nat) : Reach9 empty9 ⟨k, 0, 0⟩ k := by
  induction k with
  | zero => exact Reach9.refl empty9
  | succ j ih =>
    exact Reach9.step ih (Step9.addTerm ⟨j, 0, 0⟩)

/-- Adding r-assertions one by one. -/
theorem reach9_addR (n : Nat) (hn : n ≥ 1) (j : Nat) : Reach9 ⟨n, 0, 0⟩ ⟨n, j, 0⟩ j := by
  induction j with
  | zero => exact Reach9.refl ⟨n, 0, 0⟩
  | succ k ih =>
    exact Reach9.step ih (Step9.addAssertionR ⟨n, k, 0⟩ hn)

/-- Adding s-assertions one by one. -/
theorem reach9_addS (n r : Nat) (hn : n ≥ 1) (j : Nat) : Reach9 ⟨n, r, 0⟩ ⟨n, r, j⟩ j := by
  induction j with
  | zero => exact Reach9.refl ⟨n, r, 0⟩
  | succ k ih =>
    exact Reach9.step ih (Step9.addAssertionS ⟨n, r, k⟩ hn)

/-- Additions alone reach every well-formed state from `empty9` in `g.size` changes. -/
theorem reach9_by_additions {g : NDSt} (hw : g.WF) : Reach9 empty9 g g.size := by
  by_cases hn : g.n = 0
  · have h0 := hw hn
    have hg : g = empty9 := by
      ext
      · exact hn
      · exact h0.1
      · exact h0.2
    subst hg
    rw [empty9_size]
    exact Reach9.refl empty9
  · have hpos : g.n ≥ 1 := by omega
    have h1 := reach9_addTerms g.n
    have h2 := reach9_addR g.n hpos g.r
    have h3 := reach9_addS g.n g.r hpos g.s
    have h12 := Reach9.trans h1 h2
    have h123 : Reach9 empty9 ⟨g.n, g.r, g.s⟩ (g.n + g.r + g.s) := Reach9.trans h12 h3
    have hg : (⟨g.n, g.r, g.s⟩ : NDSt) = g := rfl
    have hsz : g.n + g.r + g.s = g.size := rfl
    rw [hg, hsz] at h123
    exact h123

/-- Additions alone reach every well-formed state from `empty9` in `g.size` changes of Problem 10. -/
theorem reach10_by_additions {g : NDSt} (hw : g.WF) : Reach10 empty9 g g.size :=
  (reach9_by_additions hw).toReach10

/-- **Fewest changes from empty.**
The minimum number of changes to reach `g` from `empty9` is exactly `g.size`,
identical to the Ninth derivation. -/
theorem fewest_changes10_empty (g : NDSt) (hw : g.WF) :
    Reach10 empty9 g g.size ∧ ∀ n : Nat, Reach10 empty9 g n → g.size ≤ n :=
  ⟨reach10_by_additions hw, fun _ h => fewest_changes10_lower h⟩

/-! ## Cost reductions between states -/

/-- An asymmetric state reaches its swapped counterpart in exactly 1 change. -/
theorem reach10_swap (s : NDSt) (hdiff : s.swap ≠ s) : Reach10 s s.swap 1 :=
  Reach10.step (Reach10.refl s) (Step10.swap s hdiff)

/-- Parity of size along any sequence of Ninth changes. -/
theorem Reach9.size_parity {s t : NDSt} {n : Nat} (h : Reach9 s t n) :
    (s.size + t.size + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step with e | e <;> omega

/-- In the Ninth derivation, any sequence from `s` to `s.swap` has even length. -/
theorem reach9_swap_even {s : NDSt} {n : Nat} (hw : s.WF) (h : Reach9 s s.swap n) :
    n % 2 = 0 := by
  have hpar := h.size_parity
  have hsz : s.swap.size = s.size := swap_size s
  rw [hsz] at hpar
  omega

/-- Zero steps implies identical state. -/
theorem Reach9.eq_of_zero {s t : NDSt} (h : Reach9 s t 0) : t = s := by
  cases h
  rfl

/-- In the Ninth derivation, if `s ≠ s.swap`, any sequence between them requires at least 2 changes. -/
theorem reach9_swap_ge_two {s : NDSt} {n : Nat} (hw : s.WF) (hdiff : s ≠ s.swap)
    (h : Reach9 s s.swap n) : 2 ≤ n := by
  have heven := reach9_swap_even hw h
  cases n with
  | zero =>
    have := h.eq_of_zero
    exact absurd this.symm hdiff
  | succ n1 =>
    cases n1 with
    | zero =>
      omega
    | succ n2 =>
      omega

/-- **Strict cost reduction**: for any asymmetric state, Problem 10 reaches `s.swap`
in 1 change, whereas Ninth requires at least 2 changes. -/
theorem swap_cost_reduction {s : NDSt} (hw : s.WF) (hdiff : s.swap ≠ s) :
    Reach10 s s.swap 1 ∧ (∀ n : Nat, Reach9 s s.swap n → 2 ≤ n) :=
  ⟨reach10_swap s hdiff, fun _ h => reach9_swap_ge_two hw (Ne.symm hdiff) h⟩

/-! ## What does not follow -/

/-- What does not follow: it does not follow that swap reduces shortest cost from empty9. -/
theorem what_does_not_follow_empty_cost_reduction (g : NDSt) (hw : g.WF) :
    ∀ n : Nat, Reach10 empty9 g n → g.size ≤ n :=
  fun _ h => fewest_changes10_lower h

/-- What does not follow: it does not follow that Ninth shortest costs are preserved
between all pairs of states. -/
theorem what_does_not_follow_ninth_costs_equal {s : NDSt} (hw : s.WF) (hdiff : s.swap ≠ s) :
    Reach10 s s.swap 1 ∧ ¬ Reach9 s s.swap 1 := by
  refine ⟨reach10_swap s hdiff, ?_⟩
  intro h1
  have := reach9_swap_ge_two hw (Ne.symm hdiff) h1
  omega

#print axioms swap_involution
#print axioms swap_size
#print axioms swap_wf
#print axioms swap_empty
#print axioms Step10.wf
#print axioms Step10.size_step
#print axioms Step10.size_le
#print axioms Reach10.size_le
#print axioms fewest_changes10_lower
#print axioms reach10_by_additions
#print axioms fewest_changes10_empty
#print axioms reach10_swap
#print axioms reach9_swap_even
#print axioms reach9_swap_ge_two
#print axioms swap_cost_reduction
#print axioms what_does_not_follow_empty_cost_reduction
#print axioms what_does_not_follow_ninth_costs_equal

end Seed.Problem10
