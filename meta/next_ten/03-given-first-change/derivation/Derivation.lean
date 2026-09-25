/-!
# Problem 03: Given First Change — Lean 4 Formal Derivation

Seed edit from Ninth seed:
"Given: one change adding a term has been made, and its outcome is the beginning.
Nothing else is given."

In the ninth derivation, the beginning was `empty` (0 terms, 0 assertions).
The first change from `empty` can only add a term.
In Problem 03, that first change has already occurred.
The beginning state `root03` has exactly 1 term and 0 assertions.

Formalized here:
1. `DState`: two-relation directed multigraph representation.
2. `root03`: beginning state obtained by adding a term to `empty`.
3. Well-formedness and non-emptiness of `root03`.
4. Step transitions: IDENTIFY, REMOVE (r and s), ADD_TERM, ADD_ASSERTION (r and s).
5. Non-emptiness invariant: every step on a state with n ≥ 1 preserves n ≥ 1.
6. The empty state is never reachable from `root03`.
7. Refutation of the candidate falsifier and resolution of the hypothesis.
-/

set_option linter.unusedVariables false

@[ext]
structure DState where
  n : Nat
  r : Nat → Nat → Nat
  s : Nat → Nat → Nat

namespace DState

/-- Well-formedness: all positive multiplicity assertions reference indices < n. -/
def WF (st : DState) : Prop :=
  ∀ x y, (st.r x y > 0 ∨ st.s x y > 0) → x < st.n ∧ y < st.n

/-- The empty state with 0 terms and 0 assertions. -/
def empty : DState :=
  ⟨0, fun _ _ => 0, fun _ _ => 0⟩

theorem empty_wf : empty.WF := by
  intro x y h
  rcases h with hr | hs <;> contradiction

/-- Adding a term to a state increases term count by 1 and extends grids with 0. -/
def addTerm (st : DState) : DState :=
  ⟨st.n + 1,
   fun x y => if x < st.n ∧ y < st.n then st.r x y else 0,
   fun x y => if x < st.n ∧ y < st.n then st.s x y else 0⟩

/-- The beginning state of Problem 03: the outcome of adding a term to empty. -/
def root03 : DState := addTerm empty

theorem root03_n : root03.n = 1 := rfl

theorem root03_r (x y : Nat) : root03.r x y = 0 := by
  dsimp [root03, addTerm, empty]

theorem root03_s (x y : Nat) : root03.s x y = 0 := by
  dsimp [root03, addTerm, empty]

/-- The beginning state has at least one term. -/
theorem root03_nonempty : root03.n > 0 := by
  dsimp [root03_n]
  omega

/-- The beginning state is well-formed. -/
theorem root03_wf : root03.WF := by
  intro x y h
  rw [root03_r x y, root03_s x y] at h
  rcases h with hr | hs <;> contradiction

/-! ## Step Operations -/

def addAssertionR (st : DState) (x y : Nat) : DState :=
  ⟨st.n, fun u v => if u = x ∧ v = y then st.r u v + 1 else st.r u v, st.s⟩

def addAssertionS (st : DState) (x y : Nat) : DState :=
  ⟨st.n, st.r, fun u v => if u = x ∧ v = y then st.s u v + 1 else st.s u v⟩

def removeAssertionR (st : DState) (x y : Nat) : DState :=
  ⟨st.n, fun u v => if u = x ∧ v = y then st.r u v - 1 else st.r u v, st.s⟩

def removeAssertionS (st : DState) (x y : Nat) : DState :=
  ⟨st.n, st.r, fun u v => if u = x ∧ v = y then st.s u v - 1 else st.s u v⟩

def mergedIndex (x y t : Nat) : Nat :=
  if t = y then (if x < y then x else x - 1)
  else if t < y then t else t - 1

/-- Identification sums every source assertion into its renamed pair. -/
def mergedMultiplicity (n : Nat) (M : Nat → Nat → Nat) (x y u v : Nat) : Nat :=
  (List.range n).foldl (fun acc a =>
    acc + (List.range n).foldl (fun inner b =>
      if mergedIndex x y a = u ∧ mergedIndex x y b = v
      then inner + M a b else inner) 0) 0

def identifyTerms (st : DState) (x y : Nat) : DState :=
  ⟨st.n - 1,
   mergedMultiplicity st.n st.r x y,
   mergedMultiplicity st.n st.s x y⟩

/-! ## Step Relation -/

inductive Step : DState → DState → Prop
  | addTerm (st : DState) : Step st (addTerm st)
  | addR (st : DState) (x y : Nat) (hx : x < st.n) (hy : y < st.n) :
      Step st (addAssertionR st x y)
  | addS (st : DState) (x y : Nat) (hx : x < st.n) (hy : y < st.n) :
      Step st (addAssertionS st x y)
  | removeR (st : DState) (x y : Nat) (hpos : st.r x y > 0) :
      Step st (removeAssertionR st x y)
  | removeS (st : DState) (x y : Nat) (hpos : st.s x y > 0) :
      Step st (removeAssertionS st x y)
  | identify (st : DState) (x y : Nat) (hx : x < st.n) (hy : y < st.n) (hne : x ≠ y) :
      Step st (identifyTerms st x y)

/-- The outcome of one change adding a term to empty is root03. -/
theorem root03_is_add_term_outcome : Step empty root03 :=
  Step.addTerm empty

/-! ## Non-Emptiness Preservation Invariant -/

/-- Every single step on a state with at least one term yields a state with at least one term. -/
theorem step_nonempty {st u : DState} (h : Step st u) (hne : st.n > 0) : u.n > 0 := by
  cases h with
  | addTerm =>
    dsimp [addTerm]
    omega
  | addR x y hx hy =>
    dsimp [addAssertionR]
    exact hne
  | addS x y hx hy =>
    dsimp [addAssertionS]
    exact hne
  | removeR x y hpos =>
    dsimp [removeAssertionR]
    exact hne
  | removeS x y hpos =>
    dsimp [removeAssertionS]
    exact hne
  | identify x y hx hy hne_xy =>
    dsimp [identifyTerms]
    have : st.n ≥ 2 := by omega
    omega

/-! ## Multi-Step Reachability -/

inductive Reach : DState → DState → Nat → Prop
  | refl (st : DState) : Reach st st 0
  | step {st u v : DState} {k : Nat} (h1 : Step st u) (h2 : Reach u v k) : Reach st v (k + 1)

/-- Any sequence of steps from a nonempty state reaches only nonempty states. -/
theorem reach_nonempty {st u : DState} {k : Nat} (h : Reach st u k) (hne : st.n > 0) : u.n > 0 := by
  induction h with
  | refl s => exact hne
  | step h1 h2 ih =>
    have hu_ne : _ > 0 := step_nonempty h1 hne
    exact ih hu_ne

/-! ## Unreachability of the Empty State -/

/-- The empty state is never reachable from root03 in k steps. -/
theorem empty_not_reachable_from_root03 (k : Nat) : ¬ Reach root03 empty k := by
  intro h
  have h_ne := reach_nonempty h root03_nonempty
  dsimp [empty] at h_ne
  contradiction

/-- The empty state is not a result in Problem 03. -/
theorem empty_not_result03 : ¬ ∃ k, Reach root03 empty k := by
  rintro ⟨k, h⟩
  exact empty_not_reachable_from_root03 k h

/-! ## Counting Assertions and Size -/

def sumRow (m : Nat) (f : Nat → Nat) : Nat :=
  match m with
  | 0 => 0
  | k + 1 => sumRow k f + f k

def sumGrid (r c : Nat) (M : Nat → Nat → Nat) : Nat :=
  match r with
  | 0 => 0
  | k + 1 => sumGrid k c M + sumRow c (M k)

def totalAssertions (st : DState) : Nat :=
  sumGrid st.n st.n st.r + sumGrid st.n st.n st.s

def size (st : DState) : Nat :=
  st.n + totalAssertions st

theorem root03_total : totalAssertions root03 = 0 := by
  dsimp [totalAssertions, root03, addTerm, empty, sumGrid, sumRow]

theorem root03_size : size root03 = 1 := by
  dsimp [size, root03_n]
  rw [root03_total]

/-! ## Falsifier Refutation and Hypothesis Resolution -/

/-- The candidate falsifier "The empty result and one-term result have the ninth's
    rounds after aligning beginnings" is refuted because the empty state is unreachable
    at any round from root03. -/
theorem falsifier_refuted :
    ¬ ∃ k, Reach root03 empty k :=
  empty_not_result03

/-- Candidate hypothesis "A given change shifts reachability and cost without a given assertion":
    root03 has 0 given assertions, yet the empty state is strictly excluded from results. -/
theorem hypothesis_supported_empty_excluded :
    totalAssertions root03 = 0 ∧ ¬ ∃ k, Reach root03 empty k :=
  ⟨root03_total, empty_not_result03⟩

end DState
