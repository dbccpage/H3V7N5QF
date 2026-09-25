/-!
# Problem 06: Written Budget — Lean 4 Formal Derivation

Seed edit from Ninth:
"Nothing is given: to begin with there are no terms and nothing is asserted.
Each alternative begins with four changes available; each performed change uses one,
an attempt with none available changes nothing, and every result records how many remain."

This formalization establishes in this model:
1. Strictly decreasing budget: every performed change consumes exactly 1 budget unit.
2. Four-step maximum bound: every path of performed changes from (empty, 4) has length at most 4.
3. Stopping at budget zero: no change can be performed once budget reaches zero.
4. Reachability characterization: a state is reachable from (empty, 4) in n steps iff
   n ≤ 4, remaining budget is 4 - n, and the underlying state is reachable in n ninth-steps.
5. Term bound: all reachable states have at most 4 terms.

Checked without `sorry`, `admit`, or non-standard axioms.
-/

set_option linter.unusedVariables false

structure State where
  n : Nat
  Mr : Nat → Nat → Nat
  Ms : Nat → Nat → Nat

namespace State

def WF (s : State) : Prop :=
  (∀ x y, s.Mr x y > 0 → x < s.n ∧ y < s.n) ∧
  (∀ x y, s.Ms x y > 0 → x < s.n ∧ y < s.n)

def empty : State :=
  ⟨0, fun _ _ => 0, fun _ _ => 0⟩

theorem empty_wf : empty.WF := by
  constructor <;> (intro x y h; contradiction)

def mergedIndex (u v t : Nat) : Nat :=
  if t = v then (if u < v then u else u - 1)
  else if t < v then t else t - 1

def mergedMultiplicity (n : Nat) (M : Nat → Nat → Nat) (u v x y : Nat) : Nat :=
  (List.range n).foldl (fun acc a =>
    acc + (List.range n).foldl (fun inner b =>
      if mergedIndex u v a = x ∧ mergedIndex u v b = y
      then inner + M a b else inner) 0) 0

-- Four kinds of changes on State
inductive Step : State → State → Prop where
  | addTerm (s : State) :
      Step s ⟨s.n + 1,
              fun x y => if x < s.n ∧ y < s.n then s.Mr x y else 0,
              fun x y => if x < s.n ∧ y < s.n then s.Ms x y else 0⟩
  | addAssertionR (s : State) (x y : Nat) (hx : x < s.n) (hy : y < s.n) :
      Step s ⟨s.n,
              fun u v => if u = x ∧ v = y then s.Mr u v + 1 else s.Mr u v,
              s.Ms⟩
  | addAssertionS (s : State) (x y : Nat) (hx : x < s.n) (hy : y < s.n) :
      Step s ⟨s.n,
              s.Mr,
              fun u v => if u = x ∧ v = y then s.Ms u v + 1 else s.Ms u v⟩
  | removeR (s : State) (x y : Nat) (hp : s.Mr x y > 0) :
      Step s ⟨s.n,
              fun u v => if u = x ∧ v = y then s.Mr u v - 1 else s.Mr u v,
              s.Ms⟩
  | removeS (s : State) (x y : Nat) (hp : s.Ms x y > 0) :
      Step s ⟨s.n,
              s.Mr,
              fun u v => if u = x ∧ v = y then s.Ms u v - 1 else s.Ms u v⟩
  | identify (s : State) (u v : Nat) (hu : u < s.n) (hv : v < s.n) (hne : u ≠ v) :
      Step s ⟨s.n - 1,
              mergedMultiplicity s.n s.Mr u v,
              mergedMultiplicity s.n s.Ms u v⟩

-- Multi-step reachability without budget
inductive Reach : State → State → Nat → Prop where
  | refl (s : State) : Reach s s 0
  | step {s t u : State} {n : Nat} : Reach s t n → Step t u → Reach s u (n + 1)

end State

-- Budgeted State
structure BState where
  state : State
  budget : Nat

namespace BState

def emptyB : BState :=
  ⟨State.empty, 4⟩

def WF (s : BState) : Prop :=
  s.state.WF ∧ s.budget ≤ 4

theorem emptyB_wf : emptyB.WF := by
  dsimp [emptyB, WF]
  exact ⟨State.empty_wf, by decide⟩

-- Performed change uses 1 budget unit and requires budget > 0
inductive BStep : BState → BState → Prop where
  | step (s : BState) (t : State) (hst : State.Step s.state t) (hb : s.budget > 0) :
      BStep s ⟨t, s.budget - 1⟩

-- Sequence of performed changes
inductive BReach : BState → BState → Nat → Prop where
  | refl (s : BState) : BReach s s 0
  | step {s t u : BState} {n : Nat} : BReach s t n → BStep t u → BReach s u (n + 1)

/-! ## 1. Strictly Decreasing Budget -/

theorem BStep.budget_eq {s t : BState} (h : BStep s t) : s.budget = t.budget + 1 := by
  cases h with
  | step t' hst hb =>
    dsimp
    omega

theorem BStep.budget_lt {s t : BState} (h : BStep s t) : t.budget < s.budget := by
  have := BStep.budget_eq h
  omega

theorem BReach.budget_eq {s t : BState} {n : Nat} (h : BReach s t n) : s.budget = t.budget + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := BStep.budget_eq st
    omega

theorem BReach.budget_le {s t : BState} {n : Nat} (h : BReach s t n) : t.budget ≤ s.budget := by
  have := BReach.budget_eq h
  omega

theorem BReach.strictly_decreasing {s t : BState} {n : Nat} (h : BReach s t n) (hn : n > 0) :
    t.budget < s.budget := by
  have := BReach.budget_eq h
  omega

/-! ## 2. Four-Step Maximum Bound and Termination at Budget Zero -/

theorem BReach.four_step_max {t : BState} {n : Nat} (h : BReach emptyB t n) : n ≤ 4 := by
  have heq := BReach.budget_eq h
  dsimp [emptyB] at heq
  omega

theorem BReach.budget_val {t : BState} {n : Nat} (h : BReach emptyB t n) : t.budget = 4 - n := by
  have heq := BReach.budget_eq h
  dsimp [emptyB] at heq
  omega

theorem BReach.budget_zero_iff_four {t : BState} {n : Nat} (h : BReach emptyB t n) :
    t.budget = 0 ↔ n = 4 := by
  have heq := BReach.budget_eq h
  dsimp [emptyB] at heq
  omega

theorem BStep.not_step_at_zero {t : BState} (hb : t.budget = 0) : ¬ ∃ u, BStep t u := by
  rintro ⟨u, hstep⟩
  cases hstep with
  | step t' hst hpos =>
    omega

/-! ## 3. Reachability Characterization -/

theorem BReach.to_reach {s t : BState} {n : Nat} (h : BReach s t n) :
    State.Reach s.state t.state n := by
  induction h with
  | refl => exact State.Reach.refl _
  | step r st ih =>
    cases st with
    | step t' hst hb =>
      exact State.Reach.step ih hst

theorem Reach.to_breach {s_st t_st : State} {n : Nat} (h : State.Reach s_st t_st n) :
    ∀ (s : BState), s.state = s_st → n ≤ s.budget →
    ∃ t : BState, t.state = t_st ∧ t.budget = s.budget - n ∧ BReach s t n := by
  induction h with
  | refl =>
    intro s hs hn
    refine ⟨s, hs, ?_, BReach.refl s⟩
    omega
  | step hr st ih =>
    rename_i t_mid u_st k
    intro s hs hn
    have hkn : k ≤ s.budget := by omega
    obtain ⟨t_bmid, ht_state, ht_budget, hreach_mid⟩ := ih s hs hkn
    have hpos : t_bmid.budget > 0 := by omega
    have hstep_st : State.Step t_bmid.state u_st := by
      rw [ht_state]
      exact st
    have hstep : BStep t_bmid ⟨u_st, t_bmid.budget - 1⟩ :=
      BStep.step t_bmid u_st hstep_st hpos
    refine ⟨⟨u_st, t_bmid.budget - 1⟩, rfl, ?_, BReach.step hreach_mid hstep⟩
    dsimp
    omega

theorem BReach.of_reach {s : BState} {t_st : State} {n : Nat}
    (h : State.Reach s.state t_st n) (hn : n ≤ s.budget) :
    ∃ t : BState, t.state = t_st ∧ t.budget = s.budget - n ∧ BReach s t n :=
  Reach.to_breach h s rfl hn

theorem BReach.characterization (t : BState) (n : Nat) :
    BReach emptyB t n ↔ (n ≤ 4 ∧ t.budget = 4 - n ∧ State.Reach State.empty t.state n) := by
  constructor
  · intro h
    refine ⟨BReach.four_step_max h, BReach.budget_val h, BReach.to_reach h⟩
  · rintro ⟨hn, hb, hr⟩
    have hbnd : n ≤ emptyB.budget := by dsimp [emptyB]; omega
    obtain ⟨t', ht'_state, ht'_budget, hreach⟩ := BReach.of_reach hr hbnd
    have ht_eq : t' = t := by
      cases t; cases t'
      dsimp at ht'_state ht'_budget hb
      dsimp [emptyB] at ht'_budget
      congr
      omega
    rw [ht_eq] at hreach
    exact hreach

/-! ## 4. Structural Bounds -/

theorem Step.terms_le {s t : State} (h : State.Step s t) : t.n ≤ s.n + 1 := by
  cases h <;> (dsimp; omega)

theorem Reach.terms_le {s t : State} {n : Nat} (h : State.Reach s t n) : t.n ≤ s.n + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have hstep := Step.terms_le st
    omega

theorem BReach.terms_le {t : BState} {n : Nat} (h : BReach emptyB t n) : t.state.n ≤ 4 := by
  have hr := BReach.to_reach h
  have hterms := Reach.terms_le hr
  have hmax := BReach.four_step_max h
  dsimp [emptyB, State.empty] at hterms
  omega

#print axioms BStep.budget_eq
#print axioms BStep.budget_lt
#print axioms BReach.budget_eq
#print axioms BReach.strictly_decreasing
#print axioms BReach.four_step_max
#print axioms BReach.budget_val
#print axioms BReach.budget_zero_iff_four
#print axioms BStep.not_step_at_zero
#print axioms BReach.to_reach
#print axioms BReach.of_reach
#print axioms BReach.characterization
#print axioms BReach.terms_le

end BState
