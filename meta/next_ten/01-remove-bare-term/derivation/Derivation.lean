/-!
# Problem 01: Remove Bare Term — Lean 4 Formal Derivation

Seed diff from Seventh:
A change is exactly one of: identifying two terms; removing an assertion;
adding a term; adding an assertion; removing a term that names no assertion.
Nothing else is a change. Identifying two terms replaces both by one term in
every assertion. Removing a term that names no assertion deletes that term
and nothing asserted.

Any outcome is valid.
-/

set_option linter.unusedVariables false

@[ext]
structure State where
  n : Nat
  M : Nat → Nat → Nat

namespace State

def WF (s : State) : Prop :=
  ∀ x y, s.M x y > 0 → x < s.n ∧ y < s.n

def empty : State :=
  ⟨0, fun _ _ => 0⟩

theorem empty_wf : empty.WF := by
  intro x y h
  contradiction

def isBare (s : State) (t : Nat) : Prop :=
  t < s.n ∧ (∀ y, s.M t y = 0) ∧ (∀ y, s.M y t = 0)

def unshift (t : Nat) (k : Nat) : Nat :=
  if k < t then k else k + 1

theorem unshift_ne (t k : Nat) : unshift t k ≠ t := by
  intro h
  dsimp [unshift] at h
  split at h <;> omega

theorem unshift_lt_sub (t x n : Nat) (ht : t < n) (h_ne : unshift t x ≠ t) (h_lt : unshift t x < n) :
    x < n - 1 := by
  dsimp [unshift] at h_ne h_lt
  split at h_ne <;> split at h_lt <;> omega

def removeBare (s : State) (t : Nat) : State :=
  ⟨s.n - 1, fun x y => s.M (unshift t x) (unshift t y)⟩

def addTerm (s : State) : State :=
  ⟨s.n + 1, fun x y => if x < s.n ∧ y < s.n then s.M x y else 0⟩

def addAssertion (s : State) (x y : Nat) : State :=
  ⟨s.n, fun u v => if u = x ∧ v = y then s.M u v + 1 else s.M u v⟩

def removeAssertion (s : State) (x y : Nat) : State :=
  ⟨s.n, fun u v => if u = x ∧ v = y then s.M u v - 1 else s.M u v⟩

-- Sum of rows and grid for counted assertions
def sumRow (m : Nat) (f : Nat → Nat) : Nat :=
  match m with
  | 0 => 0
  | k + 1 => sumRow k f + f k

def sumGrid (r c : Nat) (M : Nat → Nat → Nat) : Nat :=
  match r with
  | 0 => 0
  | k + 1 => sumGrid k c M + sumRow c (M k)

def mergedIndex (u v t : Nat) : Nat :=
  if t = v then (if u < v then u else u - 1)
  else if t < v then t else t - 1

/-- Add every source multiplicity into the pair named after identifying u and v. -/
def mergedMultiplicity (n : Nat) (M : Nat → Nat → Nat) (u v x y : Nat) : Nat :=
  (List.range n).foldl (fun acc a =>
    acc + (List.range n).foldl (fun inner b =>
      if mergedIndex u v a = x ∧ mergedIndex u v b = y
      then inner + M a b else inner) 0) 0

def identifyTerms (s : State) (u v : Nat) : State :=
  ⟨s.n - 1, mergedMultiplicity s.n s.M u v⟩

def total (s : State) : Nat :=
  sumGrid s.n s.n s.M

def size (s : State) : Nat :=
  s.n + s.total

/-! ## Preservation of Well-Formedness -/

theorem removeBare_wf (s : State) (t : Nat) (hw : s.WF) (hb : s.isBare t) :
    (removeBare s t).WF := by
  intro x y hpos
  dsimp [removeBare] at hpos
  have hM := hw (unshift t x) (unshift t y) hpos
  have hne_x : unshift t x ≠ t := by
    intro heq
    rw [heq] at hpos
    have hzero := hb.2.1 (unshift t y)
    omega
  have hne_y : unshift t y ≠ t := by
    intro heq
    rw [heq] at hpos
    have hzero := hb.2.2 (unshift t x)
    omega
  dsimp [removeBare]
  constructor
  · exact unshift_lt_sub t x s.n hb.1 hne_x hM.1
  · exact unshift_lt_sub t y s.n hb.1 hne_y hM.2

theorem addTerm_wf (s : State) (_hw : s.WF) : (addTerm s).WF := by
  intro x y hpos
  dsimp [addTerm] at hpos
  dsimp [addTerm]
  split at hpos
  · omega
  · contradiction

/-! ## Assertion Multiplicity Preservation under Bare-Term Removal -/

theorem sumRow_zero (m : Nat) : sumRow m (fun _ => 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    dsimp [sumRow]
    rw [ih]

theorem sumGrid_zero (r c : Nat) : sumGrid r c (fun _ _ => 0) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    dsimp [sumGrid]
    rw [ih, sumRow_zero]

theorem empty_total : empty.total = 0 := by
  dsimp [total, empty]
  exact sumGrid_zero 0 0

theorem empty_size : empty.size = 0 := rfl

/-! ## The One-Term State and the Two-Step Cycle -/

def oneTermBare : State :=
  addTerm empty

theorem oneTermBare_n : oneTermBare.n = 1 := rfl

theorem oneTermBare_M (x y : Nat) : oneTermBare.M x y = 0 := rfl

theorem oneTermBare_isBare_zero : oneTermBare.isBare 0 := by
  refine ⟨by dsimp [oneTermBare, addTerm, empty]; omega, ?_, ?_⟩
  · intro y
    exact oneTermBare_M 0 y
  · intro y
    exact oneTermBare_M y 0

theorem removeBare_oneTerm_eq_empty : removeBare oneTermBare 0 = empty := by
  ext <;> rfl

/-! ## Step Relation -/

inductive Step : State → State → Prop
  | addTerm (s : State) : Step s (addTerm s)
  | addAssertion (s : State) (x y : Nat) (hx : x < s.n) (hy : y < s.n) :
      Step s (addAssertion s x y)
  | removeAssertion (s : State) (x y : Nat) (hpos : s.M x y > 0) :
      Step s (removeAssertion s x y)
  | removeBareTerm (s : State) (t : Nat) (hb : s.isBare t) :
      Step s (removeBare s t)
  | identify (s : State) (u v : Nat) (hu : u < v) (hv : v < s.n) :
      Step s (identifyTerms s u v)

/-! ## Multi-Step Reachability -/

inductive Reach : State → State → Nat → Prop
  | refl (s : State) : Reach s s 0
  | step {s u t : State} {k : Nat} (h1 : Step s u) (h2 : Reach u t k) : Reach s t (k + 1)

/-! ## Main Theorems -/

/-- Theorem: The empty beginning reaches the one-term bare state in 1 step. -/
theorem reach_empty_to_oneTerm : Step empty oneTermBare :=
  Step.addTerm empty

/-- Theorem: The one-term bare state reaches the empty state in 1 step. -/
theorem reach_oneTerm_to_empty : Step oneTermBare empty := by
  have hb := oneTermBare_isBare_zero
  have h := Step.removeBareTerm oneTermBare 0 hb
  rw [removeBare_oneTerm_eq_empty] at h
  exact h

/-- Theorem: The Two-Step Cycle between empty and a nonempty state. -/
theorem two_step_cycle :
    ∃ s, s.n = 1 ∧ Step empty s ∧ Step s empty :=
  ⟨oneTermBare, rfl, reach_empty_to_oneTerm, reach_oneTerm_to_empty⟩

/-- Theorem: The empty beginning is reached from itself in 2 changes via a nonempty state. -/
theorem empty_returns_in_two_steps :
    Reach empty empty 2 := by
  refine Reach.step reach_empty_to_oneTerm ?_
  refine Reach.step reach_oneTerm_to_empty ?_
  exact Reach.refl empty

/-- Falsifier Refutation:
    The falsifier "No nonempty result reaches the empty beginning within two changes"
    is refuted by exhibiting `oneTermBare`, which is nonempty (n = 1) and reaches
    empty in exactly 1 change (which is ≤ 2). -/
theorem falsifier_refuted :
    ∃ s, s.n > 0 ∧ Step s empty :=
  ⟨oneTermBare, by dsimp [oneTermBare, addTerm, empty]; omega, reach_oneTerm_to_empty⟩

/-- Hypothesis Resolution:
    "A bare-term removal destroys the empty state's one-way reachability"
    is established because in the Seventh derivation, the empty state had
    in-degree 0 (unreachable from any nonempty state), whereas here it has
    incoming transitions from nonempty states. -/
theorem empty_state_in_degree_positive :
    ∃ s, s ≠ empty ∧ Step s empty := by
  refine ⟨oneTermBare, ?_, reach_oneTerm_to_empty⟩
  intro heq
  have hn : oneTermBare.n = empty.n := by rw [heq]
  dsimp [oneTermBare, addTerm, empty] at hn
  contradiction

end State
