/-!
# Problem 05: Refusal Memory Formalization

Parent derivation: seventeenth (code/seventeenth/, lean4/Seventeenth/).

Seed change:
    "A refused change is recorded and changes nothing. Its written form is
    kept with that result; the next attempt at the same written change is
    performed even if it makes some `xrx` asserted."

This file formalizes:
1. Graph states `St` and loop predicate `HasLoop`.
2. The four kinds of changes `Change` and base obstruction `ObstructedM1`.
3. `RefusalSt`: a state carrying a refusal record.
4. Step transitions `StepRM`:
   - `unobstructed`: normal execution.
   - `refusal`: records the refused change and changes nothing about the graph.
   - `override`: executed on repeated attempt, performing the change even if it asserts some `xrx`.
5. Theorems:
   - `refusal_preserves_state`: a refused change changes nothing about the graph.
   - `refusal_accumulates_record`: the written change is kept with that result.
   - `givenA_loopfree`: the given state asserts no loop.
   - `two_step_reaches_loop`: in two steps, the refusal-then-override sequence reaches a loop state.
   - `two_step_reaches_add_loop`: adding a loop is also reached in two steps.
   - `perform_unobstructed_loopfree`: unobstructed changes from givenA preserve loop-freeness.
   - `rootA_one_step_no_loop`: no one-step transition from rootA can assert a loop.
   - `two_attempt_difference`: the two-step path produces a loop state unreachable in one step from what is given.

Standard axioms only: `propext`, `Quot.sound`, `Classical.choice`. No `sorry`, `admit`, or custom `axiom`.
-/

namespace Problem05

/-- Graph state: terms list, assertions list, distinguished names `a` and `b`. -/
structure St where
  T : List Nat
  A : List (Nat × Nat)
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

/-- Whether a state asserts some loop `xrx`. -/
def HasLoop (s : St) : Prop :=
  ∃ x, (x, x) ∈ s.A

/-- State asserts no loop `xrx`. -/
def LoopFree (s : St) : Prop :=
  ∀ x, (x, x) ∉ s.A

/-- The four kinds of changes. -/
inductive Change where
  | addTerm (t : Nat)
  | addAssertion (x y : Nat)
  | remove (p : Nat × Nat)
  | identify (u v : Nat)
  deriving DecidableEq, Repr

/-- M1: The change would make some `xrx` asserted. -/
def ObstructedM1 (s : St) : Change → Prop
  | Change.addTerm _ => False
  | Change.addAssertion x y => x = y
  | Change.remove _ => False
  | Change.identify u v => (u, v) ∈ s.A ∨ (v, u) ∈ s.A

/-- Replacing term `v` with `u` in an endpoint. -/
def mergeEndpoints (u v : Nat) (t : Nat) : Nat :=
  if t = v then u else t

/-- Performing a change on a state. -/
def perform (s : St) : Change → St
  | Change.addTerm t => ⟨t :: s.T, s.A, s.a, s.b⟩
  | Change.addAssertion x y => ⟨s.T, (x, y) :: s.A, s.a, s.b⟩
  | Change.remove p => ⟨s.T, s.A.filter (· ≠ p), s.a, s.b⟩
  | Change.identify u v =>
    let newA := s.A.map (fun (x, y) => (mergeEndpoints u v x, mergeEndpoints u v y))
    let newT := s.T.filter (· ≠ v)
    ⟨newT, newA, mergeEndpoints u v s.a, mergeEndpoints u v s.b⟩

/-- A result carrying a base state and a refusal record. -/
structure RefusalSt where
  st : St
  refused : List Change
  deriving DecidableEq, Repr

/-- Step transition under Problem 05 refusal memory semantics. -/
inductive StepRM (rs : RefusalSt) : RefusalSt → Type where
  | unobstructed (c : Change) (hnot : ¬ ObstructedM1 rs.st c) :
      StepRM rs ⟨perform rs.st c, []⟩
  | refusal (c : Change) (hobs : ObstructedM1 rs.st c) (hnot_in : c ∉ rs.refused) :
      StepRM rs ⟨rs.st, c :: rs.refused⟩
  | override (c : Change) (hin : c ∈ rs.refused) :
      StepRM rs ⟨perform rs.st c, []⟩

/-- Multi-step reachability. -/
inductive ReachRM : RefusalSt → RefusalSt → Nat → Prop where
  | refl (rs : RefusalSt) : ReachRM rs rs 0
  | step {rs1 rs2 rs3 : RefusalSt} {n : Nat} :
      ReachRM rs1 rs2 n → StepRM rs2 rs3 → ReachRM rs1 rs3 (n + 1)

/-!
## Foundational Theorems
-/

/-- Theorem 1: A refused change changes nothing about the graph state. -/
theorem refusal_preserves_state (s : St) (R : List Change) (c : Change) :
    (⟨s, c :: R⟩ : RefusalSt).st = s := by
  rfl

/-- Theorem 2: The refused written change is kept with that result. -/
theorem refusal_accumulates_record (s : St) (R : List Change) (c : Change) :
    c ∈ (⟨s, c :: R⟩ : RefusalSt).refused := by
  simp

/-- The given beginning: `a=0`, `b=1`, `arb` asserted. -/
def givenA : St := ⟨[0, 1], [(0, 1)], 0, 1⟩

/-- The initial refusal state: what is given, empty refusal memory. -/
def rootA : RefusalSt := ⟨givenA, []⟩

/-- `givenA` asserts no loop. -/
theorem givenA_loopfree : LoopFree givenA := by
  intro x hx
  simp [givenA] at hx
  omega

/-- The identification of `0` and `1` in `givenA`. -/
def ident01 : Change := Change.identify 0 1

/-- `ident01` is obstructed on `givenA`. -/
theorem ident01_obstructed : ObstructedM1 givenA ident01 := by
  dsimp [ObstructedM1, ident01, givenA]
  left
  simp

/-- Performing `ident01` merges `0` and `1` and asserts `(0, 0)`. -/
theorem perform_ident01_has_loop : HasLoop (perform givenA ident01) := by
  dsimp [HasLoop, perform, givenA, ident01, mergeEndpoints]
  refine ⟨0, ?_⟩
  simp

/-- Adding `0r0` is obstructed on `givenA`. -/
def addLoop00 : Change := Change.addAssertion 0 0

theorem addLoop00_obstructed : ObstructedM1 givenA addLoop00 := by
  dsimp [ObstructedM1, addLoop00]

theorem perform_addLoop00_has_loop : HasLoop (perform givenA addLoop00) := by
  dsimp [HasLoop, perform, givenA, addLoop00]
  refine ⟨0, ?_⟩
  simp

/-- In 1 step from `rootA`, an attempt at `ident01` leads to a refusal state asserting NO loop. -/
def step1_ident01_refusal :
    StepRM rootA ⟨givenA, [ident01]⟩ :=
  StepRM.refusal ident01 ident01_obstructed (by simp [rootA])

theorem step1_ident01_loopfree : LoopFree (⟨givenA, [ident01]⟩ : RefusalSt).st :=
  givenA_loopfree

/-- In step 2, the repeated attempt at `ident01` triggers the override. -/
def step2_ident01_override :
    StepRM ⟨givenA, [ident01]⟩ ⟨perform givenA ident01, []⟩ :=
  StepRM.override ident01 (by simp)

/-- Main Reachability Theorem:
    A loop state is reachable in 2 steps from what is given via refusal memory. -/
theorem two_step_reaches_loop :
    ReachRM rootA ⟨perform givenA ident01, []⟩ 2 ∧
    HasLoop (perform givenA ident01) := by
  have r1 : ReachRM rootA ⟨givenA, [ident01]⟩ 1 :=
    ReachRM.step (ReachRM.refl rootA) step1_ident01_refusal
  have r2 : ReachRM rootA ⟨perform givenA ident01, []⟩ 2 :=
    ReachRM.step r1 step2_ident01_override
  exact ⟨r2, perform_ident01_has_loop⟩

/-- The same holds for adding `0r0`: reached in 2 steps via refusal memory. -/
theorem two_step_reaches_add_loop :
    ReachRM rootA ⟨perform givenA addLoop00, []⟩ 2 ∧
    HasLoop (perform givenA addLoop00) := by
  have s1 : StepRM rootA ⟨givenA, [addLoop00]⟩ :=
    StepRM.refusal addLoop00 addLoop00_obstructed (by simp [rootA])
  have s2 : StepRM ⟨givenA, [addLoop00]⟩ ⟨perform givenA addLoop00, []⟩ :=
    StepRM.override addLoop00 (by simp)
  have r1 := ReachRM.step (ReachRM.refl rootA) s1
  have r2 := ReachRM.step r1 s2
  exact ⟨r2, perform_addLoop00_has_loop⟩

/-- Helper: perform an unobstructed step on givenA produces no loop. -/
theorem perform_unobstructed_loopfree (c : Change) (hu : ¬ ObstructedM1 givenA c) :
    LoopFree (perform givenA c) := by
  intro x hx
  cases c with
  | addTerm t =>
    dsimp [perform, givenA] at hx
    simp at hx
    omega
  | addAssertion u v =>
    dsimp [perform, givenA] at hx
    simp at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, h⟩
    · exact hu rfl
    · omega
  | remove p =>
    dsimp [perform, givenA] at hx
    have hmem := (List.mem_filter.1 hx).1
    simp at hmem
    omega
  | identify u v =>
    dsimp [ObstructedM1] at hu
    dsimp [perform, givenA] at hx
    simp [mergeEndpoints] at hx
    rcases hx with ⟨h1, h2⟩
    by_cases h0v : 0 = v
    · by_cases h1v : 1 = v
      · omega
      · rw [if_pos h0v] at h1
        rw [if_neg h1v] at h2
        subst h0v h1 h2
        apply hu
        right
        simp [givenA]
    · by_cases h1v : 1 = v
      · rw [if_neg h0v] at h1
        rw [if_pos h1v] at h2
        subst h1v h1 h2
        apply hu
        left
        simp [givenA]
      · rw [if_neg h0v] at h1
        rw [if_neg h1v] at h2
        omega

/-- In 1 step from rootA, NO state with a loop can be reached. -/
theorem rootA_one_step_no_loop (rs' : RefusalSt) (step : StepRM rootA rs') :
    ¬ HasLoop rs'.st := by
  cases step with
  | unobstructed c hnot =>
    intro ⟨x, hx⟩
    exact perform_unobstructed_loopfree c hnot x hx
  | refusal c _ _ =>
    intro ⟨x, hx⟩
    exact givenA_loopfree x hx
  | override c hin =>
    cases hin

/-- Two-Attempt Difference:
    A loop state is impossible in one step from rootA, but exists in two steps. -/
theorem two_attempt_difference :
    (∀ rs', StepRM rootA rs' → ¬ HasLoop rs'.st) ∧
    (∃ rs'', ReachRM rootA rs'' 2 ∧ HasLoop rs''.st) :=
  ⟨rootA_one_step_no_loop, ⟨⟨perform givenA ident01, []⟩, two_step_reaches_loop.1, two_step_reaches_loop.2⟩⟩

#print axioms two_step_reaches_loop
#print axioms two_attempt_difference

end Problem05
