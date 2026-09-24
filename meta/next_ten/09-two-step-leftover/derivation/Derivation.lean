/-!
# Problem 09: Two-Step Leftover Clearance Formalization

Seed edit from Tenth seed:
- "Nothing left, a leftover that a later change of the four kinds can clear, and a leftover that none of them can, are three outcomes. Declare which, for every change."
+ "Nothing left, a leftover that a sequence of at most two later changes of the four kinds can clear, and a leftover that no such sequence can clear, are three outcomes. Declare which, for every change."

This file formalizes:
1. Abstract state metrics: term count `n` and assertion count `m`.
2. The four kinds of changes and their effects on `(n, m)`.
3. Multi-step reachability and the Size Parity Invariant.
4. Proof that no identification can be restored in exactly 2 steps.
5. Equivalence theorem: every two-step clearable leftover is one-step clearable,
   refuting the hypothesis and proving the falsifier.
-/

namespace Problem09

open Classical

/-- The three leftover outcomes declared by the seed. -/
inductive LeftOver where
  | nothingLeft : LeftOver
  | clearable   : LeftOver
  | uncleared   : LeftOver
deriving DecidableEq, Repr

/-- Abstract state metrics: number of terms `n` and total assertion multiplicity `m`. -/
@[ext]
structure StateMetrics where
  n : Nat
  m : Nat
deriving DecidableEq, Repr

/-- Total size of a state: terms plus assertions. -/
def StateMetrics.size (s : StateMetrics) : Nat := s.n + s.m

/-- The four kinds of changes declared by the seed. -/
inductive Kind where
  | addTerm          : Kind
  | identify         : Kind
  | addAssertion     : Kind
  | removeAssertion  : Kind
deriving DecidableEq, Repr

/-- Single change step relation on state metrics. -/
inductive Step : StateMetrics → StateMetrics → Kind → Prop where
  | addTerm (s : StateMetrics) :
      Step s ⟨s.n + 1, s.m⟩ Kind.addTerm
  | identify (s : StateMetrics) (hn : s.n ≥ 2) :
      Step s ⟨s.n - 1, s.m⟩ Kind.identify
  | addAssertion (s : StateMetrics) :
      Step s ⟨s.n, s.m + 1⟩ Kind.addAssertion
  | removeAssertion (s : StateMetrics) (hm : s.m ≥ 1) :
      Step s ⟨s.n, s.m - 1⟩ Kind.removeAssertion

/-- Reachability in exactly `k` steps. -/
inductive Reach : StateMetrics → StateMetrics → Nat → Prop where
  | refl (s : StateMetrics) :
      Reach s s 0
  | step {s t u : StateMetrics} {k : Nat} {knd : Kind} :
      Reach s t k → Step t u knd → Reach s u (k + 1)

/-- Isomorphism / equivalence of state metrics: same number of terms and assertions. -/
def EquivState (s t : StateMetrics) : Prop :=
  s.n = t.n ∧ s.m = t.m

/-- An outcome can be restored in at most `k` steps if some sequence of length ≤ k reaches an equivalent state. -/
def RestoresInAtMost (out start : StateMetrics) (k : Nat) : Prop :=
  ∃ len, len ≤ k ∧ ∃ res, Reach out res len ∧ EquivState res start

/-- One-step clearance of an outcome. -/
def RestoresInOne (out start : StateMetrics) : Prop :=
  RestoresInAtMost out start 1

/-- Two-step clearance of an outcome. -/
def RestoresInTwo (out start : StateMetrics) : Prop :=
  RestoresInAtMost out start 2

/-- Theorem: Zero steps can never restore an identification. -/
theorem zero_steps_cannot_restore_identify (s : StateMetrics) (hn : s.n ≥ 2) :
    ¬ RestoresInAtMost ⟨s.n - 1, s.m⟩ s 0 := by
  intro h
  rcases h with ⟨len, hlen, res, hreach, hequiv⟩
  have hlen0 : len = 0 := Nat.le_zero.mp hlen
  subst hlen0
  cases hreach with
  | refl =>
    have hn_eq := hequiv.1
    dsimp at hn_eq
    omega

/-- Theorem: Net delta of term count and multiplicity in a single step using addition instead of truncated subtraction. -/
theorem step_delta_n (s t : StateMetrics) (knd : Kind) (h : Step s t knd) :
    (t.n = s.n + 1 ∧ t.m = s.m) ∨
    (t.n + 1 = s.n ∧ t.m = s.m) ∨
    (t.n = s.n ∧ t.m = s.m + 1) ∨
    (t.n = s.n ∧ t.m + 1 = s.m) := by
  cases h with
  | addTerm => left; refine ⟨rfl, rfl⟩
  | identify hn => right; left; refine ⟨by dsimp; omega, rfl⟩
  | addAssertion => right; right; left; refine ⟨rfl, rfl⟩
  | removeAssertion hm => right; right; right; refine ⟨rfl, by dsimp; omega⟩


/-- Fundamental Lemma: Any 2-step continuation that achieves Δn = +1 must have Δm ≠ 0.
    Specifically, it requires 1 addTerm (Δn=+1, Δm=0) and 1 assertion change (Δn=0, Δm=±1),
    yielding net Δm = ±1 ≠ 0. -/
theorem two_step_term_increase_has_assertion_delta
    (out t res : StateMetrics) (knd1 knd2 : Kind)
    (h1 : Step out t knd1) (h2 : Step t res knd2)
    (hn : res.n = out.n + 1) :
    res.m = out.m + 1 ∨ res.m + 1 = out.m := by
  have d1 := step_delta_n out t knd1 h1
  have d2 := step_delta_n t res knd2 h2
  rcases d1 with (⟨hn1, hm1⟩ | ⟨hn1, hm1⟩ | ⟨hn1, hm1⟩ | ⟨hn1, hm1⟩) <;>
  rcases d2 with (⟨hn2, hm2⟩ | ⟨hn2, hm2⟩ | ⟨hn2, hm2⟩ | ⟨hn2, hm2⟩) <;>
  omega

/-- Theorem: No identification can be restored in exactly 2 steps.
    Because an identification outcome has (n-1, m), restoring start (n, m) requires
    Δn = +1 and Δm = 0. But two steps with Δn = +1 force Δm = ±1 ≠ 0. -/
theorem two_step_cannot_restore_identify
    (s out t res : StateMetrics) (knd1 knd2 : Kind)
    (hn : s.n ≥ 2)
    (hout : out = ⟨s.n - 1, s.m⟩)
    (h1 : Step out t knd1) (h2 : Step t res knd2) :
    ¬ EquivState res s := by
  intro ⟨hn_eq, hm_eq⟩
  subst hout
  have h_delta_n : res.n = (s.n - 1) + 1 := by omega
  have h_delta_m := two_step_term_increase_has_assertion_delta ⟨s.n - 1, s.m⟩ t res knd1 knd2 h1 h2 h_delta_n
  cases h_delta_m with
  | inl h =>
    dsimp at h
    omega
  | inr h =>
    dsimp at h
    omega

/-- Theorem: Any sequence of at most 2 steps that restores an identification must restore it in at most 1 step. -/
theorem restores_in_two_identify_implies_restores_in_one
    (s : StateMetrics) (hn : s.n ≥ 2) :
    RestoresInTwo ⟨s.n - 1, s.m⟩ s → RestoresInOne ⟨s.n - 1, s.m⟩ s := by
  intro h
  rcases h with ⟨len, hlen, res, hreach, hequiv⟩
  have hlen_cases : len = 0 ∨ len = 1 ∨ len = 2 := by omega
  rcases hlen_cases with (rfl | rfl | rfl)
  · exfalso
    exact zero_steps_cannot_restore_identify s hn ⟨0, by decide, res, hreach, hequiv⟩
  · exact ⟨1, by decide, res, hreach, hequiv⟩
  · exfalso
    cases hreach with
    | step hreach1 hstep2 =>
      cases hreach1 with
      | step hreach0 hstep1 =>
        cases hreach0 with
        | refl =>
          exact two_step_cannot_restore_identify s ⟨s.n - 1, s.m⟩ _ res _ _ hn rfl hstep1 hstep2 hequiv

/-- Theorem: Restoring in at most 1 step always implies restoring in at most 2 steps. -/
theorem restores_in_one_implies_restores_in_two (out s : StateMetrics) :
    RestoresInOne out s → RestoresInTwo out s := by
  intro ⟨len, hlen, res, hreach, hequiv⟩
  exact ⟨len, by omega, res, hreach, hequiv⟩

/-- Main Equivalence Theorem for Identifications:
    An identification is 2-step clearable if and only if it is 1-step clearable. -/
theorem identify_two_step_iff_one_step (s : StateMetrics) (hn : s.n ≥ 2) :
    RestoresInTwo ⟨s.n - 1, s.m⟩ s ↔ RestoresInOne ⟨s.n - 1, s.m⟩ s := by
  constructor
  · exact restores_in_two_identify_implies_restores_in_one s hn
  · exact restores_in_one_implies_restores_in_two ⟨s.n - 1, s.m⟩ s

/-- Removal outcome is always 1-step clearable (by re-adding the assertion). -/
theorem removal_restores_in_one (s : StateMetrics) (hm : s.m ≥ 1) :
    RestoresInOne ⟨s.n, s.m - 1⟩ s := by
  refine ⟨1, by decide, s, ?_, ⟨rfl, rfl⟩⟩
  have hstep : Step ⟨s.n, s.m - 1⟩ ⟨s.n, (s.m - 1) + 1⟩ Kind.addAssertion :=
    Step.addAssertion ⟨s.n, s.m - 1⟩
  have heq : (s.m - 1) + 1 = s.m := by omega
  have hstep' : Step ⟨s.n, s.m - 1⟩ s Kind.addAssertion := by
    have h : (⟨s.n, (s.m - 1) + 1⟩ : StateMetrics) = s := by
      cases s
      dsimp at heq ⊢
      rw [heq]
    rwa [h] at hstep
  exact Reach.step (Reach.refl _) hstep'

/-- Removal outcome is always 2-step clearable. -/
theorem removal_restores_in_two (s : StateMetrics) (hm : s.m ≥ 1) :
    RestoresInTwo ⟨s.n, s.m - 1⟩ s :=
  restores_in_one_implies_restores_in_two ⟨s.n, s.m - 1⟩ s (removal_restores_in_one s hm)

/-- Definition of Leftover under Problem 09 seed (at most 2 steps). -/
noncomputable def leftoverTwoStep (s : StateMetrics) (knd : Kind) : LeftOver :=
  match knd with
  | Kind.addTerm => LeftOver.nothingLeft
  | Kind.addAssertion => LeftOver.nothingLeft
  | Kind.removeAssertion => LeftOver.clearable
  | Kind.identify =>
      if RestoresInTwo ⟨s.n - 1, s.m⟩ s then LeftOver.clearable else LeftOver.uncleared

/-- Definition of Leftover under Tenth seed (1 step). -/
noncomputable def leftoverOneStep (s : StateMetrics) (knd : Kind) : LeftOver :=
  match knd with
  | Kind.addTerm => LeftOver.nothingLeft
  | Kind.addAssertion => LeftOver.nothingLeft
  | Kind.removeAssertion => LeftOver.clearable
  | Kind.identify =>
      if RestoresInOne ⟨s.n - 1, s.m⟩ s then LeftOver.clearable else LeftOver.uncleared

/-- Complete Coincidence Theorem:
    For every state `s` and every change kind `knd`, the two-step leftover outcome
    is identical to the one-step leftover outcome. -/
theorem leftover_two_step_eq_one_step (s : StateMetrics) (knd : Kind) (hn : knd = Kind.identify → s.n ≥ 2) :
    leftoverTwoStep s knd = leftoverOneStep s knd := by
  cases knd with
  | addTerm => rfl
  | addAssertion => rfl
  | removeAssertion => rfl
  | identify =>
      dsimp [leftoverTwoStep, leftoverOneStep]
      have hn2 : s.n ≥ 2 := hn rfl
      have hiff := identify_two_step_iff_one_step s hn2
      by_cases h1 : RestoresInOne ⟨s.n - 1, s.m⟩ s
      · have h2 : RestoresInTwo ⟨s.n - 1, s.m⟩ s := hiff.mpr h1
        rw [if_pos h2, if_pos h1]
      · have h2 : ¬ RestoresInTwo ⟨s.n - 1, s.m⟩ s := mt hiff.mp h1
        rw [if_neg h2, if_neg h1]

/-- The Falsifier Theorem:
    Every two-step clearable leftover was already one-step clearable.
    (The hypothesis that two-step clearing has outcomes beyond the one-step bare-term criterion is refuted). -/
theorem falsifier_holds (s : StateMetrics) (knd : Kind) (hn : knd = Kind.identify → s.n ≥ 2) :
    leftoverTwoStep s knd = LeftOver.clearable → leftoverOneStep s knd = LeftOver.clearable := by
  intro h
  rw [← leftover_two_step_eq_one_step s knd hn]
  exact h

end Problem09
