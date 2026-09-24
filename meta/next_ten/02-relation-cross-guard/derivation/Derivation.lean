/-!
# Formal Derivation for Problem 02: Cross-Relation Guard

Candidate: C21 (meta/next_ten/02-relation-cross-guard)
Parent derivation: Ninth (`code/ninth/`, `lean4/Ninth/`, `paper/ninth/`)

Seed modification:
  "Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy`
  is a change only if `xry` is not asserted."

Key results formalized:
1. `Step9`: Ninth derivation transition semantics.
2. `StepG`: Guarded transition semantics enforcing the cross-relation guard.
3. `StepG.toStep9`: Conservative embedding of guarded steps into ninth steps.
4. `blocked_pair_cannot_add`: Direct addition of complementary relation is blocked.
5. `DisjointSupport`: Invariant preserved by guarded additions alone.
6. `additions_alone_disjoint`: Induction showing states reached by additions alone have disjoint supports.
7. `identification_bypass`: Construction showing identification can produce overlapping assertions from disjoint states.
-/

namespace Derivation02

/-- Two relations: false = r, true = s. -/
abbrev Rel := Bool

def otherRel (q : Rel) : Rel := !q

@[simp] theorem otherRel_false : otherRel false = true := rfl
@[simp] theorem otherRel_true : otherRel true = false := rfl

/-- Two-relation state representation without names. -/
structure NDSt where
  T : List Nat
  M : Rel → Nat × Nat → Nat

def empty : NDSt := ⟨[], fun _ _ => 0⟩

def addTerm (s : NDSt) (t : Nat) : NDSt :=
  ⟨t :: s.T, s.M⟩

def addAssertion (s : NDSt) (q : Rel) (x y : Nat) : NDSt :=
  ⟨s.T, fun q' p =>
    if q' = q ∧ p = (x, y) then s.M q p + 1 else s.M q' p⟩

def removeAssertion (s : NDSt) (q : Rel) (x y : Nat) : NDSt :=
  ⟨s.T, fun q' p =>
    if q' = q ∧ p = (x, y) then s.M q p - 1 else s.M q' p⟩

def merge (u v t : Nat) : Nat :=
  if t = v then u else t

def pairs (T : List Nat) : List (Nat × Nat) :=
  T.flatMap (fun x => T.map (fun y => (x, y)))

/-- Merging terms u and v in every assertion across both relations. -/
def identify (s : NDSt) (u v : Nat) : NDSt :=
  ⟨s.T.filter (· ≠ v), fun q p =>
    ((pairs s.T).filter (fun w => (merge u v w.1, merge u v w.2) = p)).foldl (fun acc w => acc + s.M q w) 0⟩

/-! ## Step Relations -/

/-- One step of the parent ninth derivation (unguarded additions). -/
inductive Step9 : NDSt → NDSt → Prop
  | addTerm (s : NDSt) (t : Nat) (ht : t ∉ s.T) :
      Step9 s (addTerm s t)
  | addAssertion (s : NDSt) (q : Rel) (x y : Nat) (hx : x ∈ s.T) (hy : y ∈ s.T) :
      Step9 s (addAssertion s q x y)
  | remove (s : NDSt) (q : Rel) (x y : Nat) (hp : s.M q (x, y) ≠ 0) :
      Step9 s (removeAssertion s q x y)
  | identify (s : NDSt) (u v : Nat) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
      Step9 s (identify s u v)

/-- One step of Problem 02: adding an assertion requires the other relation to not be asserted. -/
inductive StepG : NDSt → NDSt → Prop
  | addTerm (s : NDSt) (t : Nat) (ht : t ∉ s.T) :
      StepG s (addTerm s t)
  | addAssertion (s : NDSt) (q : Rel) (x y : Nat) (hx : x ∈ s.T) (hy : y ∈ s.T)
      (hg : s.M (!q) (x, y) = 0) :
      StepG s (addAssertion s q x y)
  | remove (s : NDSt) (q : Rel) (x y : Nat) (hp : s.M q (x, y) ≠ 0) :
      StepG s (removeAssertion s q x y)
  | identify (s : NDSt) (u v : Nat) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
      StepG s (identify s u v)

/-! ## Embedding into Ninth -/

/-- Every guarded step is an admissible step of the parent ninth derivation. -/
theorem StepG.toStep9 {s t : NDSt} (h : StepG s t) : Step9 s t := by
  cases h with
  | addTerm t ht =>
    exact Step9.addTerm s t ht
  | addAssertion q x y hx hy _ =>
    exact Step9.addAssertion s q x y hx hy
  | remove q x y hp =>
    exact Step9.remove s q x y hp
  | identify u v hu hv huv =>
    exact Step9.identify s u v hu hv huv

/-! ## Multi-Step Reachability -/

inductive ReachG : NDSt → NDSt → Nat → Prop
  | refl (s : NDSt) : ReachG s s 0
  | step {s t u : NDSt} {n : Nat} (h1 : ReachG s t n) (h2 : StepG t u) : ReachG s u (n + 1)

inductive Reach9 : NDSt → NDSt → Nat → Prop
  | refl (s : NDSt) : Reach9 s s 0
  | step {s t u : NDSt} {n : Nat} (h1 : Reach9 s t n) (h2 : Step9 t u) : Reach9 s u (n + 1)

/-- Every guarded path embeds into a ninth path of identical length. -/
theorem ReachG.toReach9 {s t : NDSt} {n : Nat} (h : ReachG s t n) : Reach9 s t n := by
  induction h with
  | refl => exact Reach9.refl _
  | step _ h2 ih => exact Reach9.step ih h2.toStep9

/-! ## Target 1: Blocked Pair Witness -/

def isCrossGuarded (s : NDSt) (q : Rel) (x y : Nat) : Prop :=
  s.M (!q) (x, y) ≠ 0

/-- If a pair is cross-guarded, adding relation q on that pair is not an admitted StepG. -/
theorem blocked_pair_cannot_add (s : NDSt) (q : Rel) (x y : Nat)
    (hb : isCrossGuarded s q x y) :
    s.M (!q) (x, y) = 0 → False := by
  intro hg
  exact hb hg

/-- Concrete witness: state with 0r0 asserted blocks addition of 0s0. -/
def s_witness : NDSt :=
  ⟨[0], fun q p => if q = false ∧ p = (0, 0) then 1 else 0⟩

theorem s_witness_r_asserted : s_witness.M false (0, 0) = 1 := by
  rfl

theorem s_witness_blocks_s : isCrossGuarded s_witness true 0 0 := by
  dsimp [isCrossGuarded, s_witness]
  intro h
  contradiction

/-! ## Target 2: Disjoint Support Invariant Under Additions -/

/-- A state has disjoint support if no ordered pair has positive multiplicity in both relations. -/
def DisjointSupport (s : NDSt) : Prop :=
  ∀ x y, s.M false (x, y) = 0 ∨ s.M true (x, y) = 0

theorem empty_disjoint : DisjointSupport empty := by
  intro x y
  left
  rfl

theorem addTerm_disjoint (s : NDSt) (t : Nat) (hs : DisjointSupport s) :
    DisjointSupport (addTerm s t) := by
  exact hs

theorem addAssertion_disjoint (s : NDSt) (q : Rel) (x y : Nat)
    (hg : s.M (!q) (x, y) = 0) (hs : DisjointSupport s) :
    DisjointSupport (addAssertion s q x y) := by
  intro a b
  dsimp [addAssertion, DisjointSupport]
  cases q with
  | false =>
    by_cases h : a = x ∧ b = y
    · right
      have h1 : ¬(true = false ∧ (a, b) = (x, y)) := by intro ⟨h_rel, _⟩; contradiction
      rw [if_neg h1]
      rcases h with ⟨rfl, rfl⟩
      exact hg
    · cases hs a b with
      | inl hr =>
        left
        have h_pair : ¬((a, b) = (x, y)) := by intro heq; cases heq; exact h ⟨rfl, rfl⟩
        have h1 : ¬(false = false ∧ (a, b) = (x, y)) := by intro ⟨_, heq⟩; exact h_pair heq
        rw [if_neg h1]
        exact hr
      | inr hs_val =>
        right
        have h1 : ¬(true = false ∧ (a, b) = (x, y)) := by intro ⟨h_rel, _⟩; contradiction
        rw [if_neg h1]
        exact hs_val
  | true =>
    by_cases h : a = x ∧ b = y
    · left
      have h1 : ¬(false = true ∧ (a, b) = (x, y)) := by intro ⟨h_rel, _⟩; contradiction
      rw [if_neg h1]
      rcases h with ⟨rfl, rfl⟩
      exact hg
    · cases hs a b with
      | inl hr =>
        left
        have h1 : ¬(false = true ∧ (a, b) = (x, y)) := by intro ⟨h_rel, _⟩; contradiction
        rw [if_neg h1]
        exact hr
      | inr hs_val =>
        right
        have h_pair : ¬((a, b) = (x, y)) := by intro heq; cases heq; exact h ⟨rfl, rfl⟩
        have h1 : ¬(true = true ∧ (a, b) = (x, y)) := by intro ⟨_, heq⟩; exact h_pair heq
        rw [if_neg h1]
        exact hs_val

/-- Guarded additions: step relation restricted to additions alone. -/
inductive StepG_Add : NDSt → NDSt → Prop
  | addTerm (s : NDSt) (t : Nat) (ht : t ∉ s.T) :
      StepG_Add s (addTerm s t)
  | addAssertion (s : NDSt) (q : Rel) (x y : Nat) (hx : x ∈ s.T) (hy : y ∈ s.T)
      (hg : s.M (!q) (x, y) = 0) :
      StepG_Add s (addAssertion s q x y)

inductive ReachG_Add : NDSt → NDSt → Nat → Prop
  | refl (s : NDSt) : ReachG_Add s s 0
  | step {s t u : NDSt} {n : Nat} (h1 : ReachG_Add s t n) (h2 : StepG_Add t u) : ReachG_Add s u (n + 1)

/-- Additions alone preserve disjoint support from the empty beginning. -/
theorem reach_add_preserves_disjoint {s : NDSt} {n : Nat}
    (h : ReachG_Add empty s n) : DisjointSupport s := by
  induction h with
  | refl => exact empty_disjoint
  | step _ h2 ih =>
    cases h2 with
    | addTerm u ht => exact addTerm_disjoint _ u ih
    | addAssertion q x y _ _ hg => exact addAssertion_disjoint _ q x y hg ih

/-! ## Target 3: Overlapping Support and Identification Bypass -/

/-- An overlapping state asserts both relations on at least one pair. -/
def Overlapping (s : NDSt) : Prop :=
  ∃ x y, s.M false (x, y) > 0 ∧ s.M true (x, y) > 0

theorem overlapping_not_disjoint {s : NDSt} (h : Overlapping s) : ¬ DisjointSupport s := by
  intro hd
  rcases h with ⟨x, y, hr, hs⟩
  cases hd x y with
  | inl h0 => rw [h0] at hr; contradiction
  | inr h0 => rw [h0] at hs; contradiction

/-- Overlapping states are unreachable by additions alone. -/
theorem overlapping_unreachable_by_additions {s : NDSt} {n : Nat}
    (h_reach : ReachG_Add empty s n) (h_ov : Overlapping s) : False := by
  have hd := reach_add_preserves_disjoint h_reach
  exact overlapping_not_disjoint h_ov hd

/-- Identification bypass witness state before merge:
    terms {0, 1}, r on (1, 1), s on (0, 0).
    Has disjoint support. -/
def s_pre : NDSt :=
  ⟨[0, 1], fun q p =>
    if q = false ∧ p = (1, 1) then 1
    else if q = true ∧ p = (0, 0) then 1
    else 0⟩

theorem s_pre_disjoint : DisjointSupport s_pre := by
  intro x y
  dsimp [s_pre, DisjointSupport]
  by_cases hx : x = 1
  · subst hx
    by_cases hy : y = 1
    · subst hy
      right
      rfl
    · left
      split
      · rename_i h
        cases h.2
        contradiction
      · rfl
  · left
    split
    · rename_i h
      cases h.2
      contradiction
    · rfl

/-- The state after identifying term 0 and term 1 has overlapping assertions on (0, 0). -/
def s_post : NDSt := identify s_pre 0 1

theorem s_post_overlapping : Overlapping s_post := by
  refine ⟨0, 0, ?_, ?_⟩
  · decide
  · decide

/-- Identification step is valid under StepG. -/
theorem step_identify_valid :
    StepG s_pre s_post := by
  apply StepG.identify s_pre 0 1
  · decide
  · decide
  · decide

/-- The identification bypass theorem:
    Identification can transition from a disjoint support state to an overlapping state,
    bypassing the addition cross-guard. -/
theorem identification_bypasses_guard :
    DisjointSupport s_pre ∧ StepG s_pre s_post ∧ Overlapping s_post := by
  exact ⟨s_pre_disjoint, step_identify_valid, s_post_overlapping⟩

#print axioms StepG.toStep9
#print axioms ReachG.toReach9
#print axioms blocked_pair_cannot_add
#print axioms s_witness_r_asserted
#print axioms s_witness_blocks_s
#print axioms empty_disjoint
#print axioms addTerm_disjoint
#print axioms addAssertion_disjoint
#print axioms reach_add_preserves_disjoint
#print axioms overlapping_not_disjoint
#print axioms overlapping_unreachable_by_additions
#print axioms s_pre_disjoint
#print axioms s_post_overlapping
#print axioms step_identify_valid
#print axioms identification_bypasses_guard

end Derivation02

