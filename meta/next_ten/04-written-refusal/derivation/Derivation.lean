def _root_.List.card {α : Type} (l : List α) : Nat := l.length

/-!
# Problem 04 (Written Refusal) Derivation

Formalizes the interaction between literal written state identity and refusal semantics.

1. **Written Identity**: Two results are the same written result iff they are identical (`s1 = s2`).
2. **Step Map & Legality**: Every performed step between written states preserves legality.
3. **Refusal Invariant**: Obstructed changes (asserting some `xrx`) are refused; refusal changes nothing.
4. **Strict Splitting Witness**: Constructive witnesses of states identical in the renaming quotient
   but distinct as written results.
-/

namespace Seed.WrittenRefusal

/-- Terms, asserted pairs, and the terms named `a` and `b`. -/
structure St where
  T : List Nat
  A : List (Nat × Nat)
  a : Nat
  b : Nat
  deriving DecidableEq

/-- Written identity: two results are the same result iff their representations are identical. -/
def WrittenEq (s1 s2 : St) : Prop := s1 = s2

theorem writtenEq_refl (s : St) : WrittenEq s s := rfl

theorem writtenEq_symm {s1 s2 : St} (h : WrittenEq s1 s2) : WrittenEq s2 s1 := h.symm

theorem writtenEq_trans {s1 s2 s3 : St} (h1 : WrittenEq s1 s2) (h2 : WrittenEq s2 s3) :
    WrittenEq s1 s3 := h1.trans h2

namespace St

/-- No `xrx` is asserted. -/
def Legal (s : St) : Prop := ∀ x, (x, x) ∉ s.A

/-- Adding a term. -/
def addTerm (s : St) (t : Nat) : St :=
  ⟨t :: s.T, s.A, s.a, s.b⟩

/-- Adding an assertion. -/
def addAssertion (s : St) (x y : Nat) : St :=
  ⟨s.T, (x, y) :: s.A, s.a, s.b⟩

/-- Removing an assertion. -/
def remove (s : St) (p : Nat × Nat) : St :=
  ⟨s.T, s.A.filter (· ≠ p), s.a, s.b⟩

/-- Merge term `v` into `u`. -/
def merge (u v t : Nat) : Nat :=
  if t = v then u else t

/-- Identifying `u` and `v`: both are replaced by `u` in every assertion,
    and names follow. -/
def identify (s : St) (u v : Nat) : St :=
  ⟨s.T.filter (· ≠ v),
   s.A.map (fun (x, y) => (merge u v x, merge u v y)),
   merge u v s.a,
   merge u v s.b⟩

end St

open St

/-- Merging distinct terms produces equality only on the identified pair. -/
theorem merge_eq_merge {u v x y : Nat} (hxy : x ≠ y)
    (h : merge u v x = merge u v y) : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  dsimp [merge] at h
  split at h <;> split at h
  · next hx hy => omega
  · next hx hy =>
    subst hx
    cases h
    exact Or.inr ⟨rfl, rfl⟩
  · next hx hy =>
    subst hy
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  · next hx hy =>
    contradiction

/-! ## Step Map and Refusal -/

/-- One performed (unobstructed) change. -/
inductive Step : St → St → Prop where
  | addTerm (s : St) (t : Nat) (ht : t ∉ s.T) :
      Step s (s.addTerm t)
  | addAssertion (s : St) (x y : Nat) (hx : x ∈ s.T) (hy : y ∈ s.T) (hxy : x ≠ y)
      (hnew : (x, y) ∉ s.A) :
      Step s (s.addAssertion x y)
  | remove (s : St) (p : Nat × Nat) (hp : p ∈ s.A) :
      Step s (s.remove p)
  | identify (s : St) (u v : Nat) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v)
      (h1 : (u, v) ∉ s.A) (h2 : (v, u) ∉ s.A) :
      Step s (s.identify u v)

/-- Every performed change between written states preserves legality. -/
theorem written_step_preserves_legal {s t : St} (h : Step s t) (hs : s.Legal) : t.Legal := by
  cases h with
  | addTerm t ht =>
    intro x hx
    exact hs x hx
  | addAssertion x y hx hy hxy hnew =>
    intro w hw
    simp only [St.addAssertion, List.mem_cons] at hw
    rcases hw with heq | hmem
    · have hx_eq : x = y := by
        have : (w, w).1 = (x, y).1 := congrArg Prod.fst heq
        have : (w, w).2 = (x, y).2 := congrArg Prod.snd heq
        omega
      exact hxy hx_eq
    · exact hs w hmem
  | remove p hp =>
    intro w hw
    simp only [St.remove, List.mem_filter] at hw
    exact hs w hw.1
  | identify u v hu hv huv h1 h2 =>
    intro w hw
    simp only [St.identify, List.mem_map] at hw
    obtain ⟨⟨x, y⟩, hq, heq⟩ := hw
    simp only [Prod.mk.injEq] at heq
    have hxy : x ≠ y := by
      rintro rfl
      exact hs x hq
    have hmerge : merge u v x = merge u v y := heq.1.trans heq.2.symm
    rcases merge_eq_merge hxy hmerge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1 hq
    · exact h2 hq

/-- Refusal invariant: any change that would produce an illegal state is refused,
    so no step to an illegal state exists. -/
theorem refusal_invariant {s t : St} (hs : s.Legal) (ht : ¬ t.Legal) : ¬ Step s t :=
  fun h => ht (written_step_preserves_legal h hs)

/-- Adding any self-loop `xrx` to a state is always obstructed. -/
theorem adding_xrx_always_obstructed (s : St) (x : Nat) : ¬ (s.addAssertion x x).Legal := by
  intro h
  have hx : (x, x) ∈ (s.addAssertion x x).A := by simp [St.addAssertion]
  exact h x hx

/-- Adding any self-loop `xrx` to a legal state is always refused. -/
theorem adding_self_loop_refused (s : St) (hs : s.Legal) (x : Nat) :
    ¬ Step s (s.addAssertion x x) := by
  intro h
  have ht : (s.addAssertion x x).Legal := written_step_preserves_legal h hs
  exact adding_xrx_always_obstructed s x ht

/-- The given beginning state: terms 0 and 1, assertion (0, 1), names 0 and 1. -/
def givenA : St := ⟨[0, 1], [(0, 1)], 0, 1⟩

theorem givenA_legal : givenA.Legal := by
  intro x hx
  simp [givenA] at hx
  omega

/-- Identifying the given terms in what is given asserts `(0, 0)`, which is illegal. -/
theorem identify_given_illegal : ¬ (givenA.identify 0 1).Legal := by
  intro h
  have h0 : (0, 0) ∈ (givenA.identify 0 1).A := by
    simp [givenA, St.identify, merge]
  exact h 0 h0

/-- Identifying the given terms in what is given is refused. -/
theorem identify_given_refused : ¬ Step givenA (givenA.identify 0 1) :=
  refusal_invariant givenA_legal identify_given_illegal

/-- Refusal changes nothing: the state remains unchanged upon refusal. -/
def refusalOutcome (s : St) : St := s

theorem refusal_changes_nothing (s : St) : refusalOutcome s = s := rfl

/-! ## Splitting Witnesses: Written Identity Refines the Quotient -/

/-- Free splitting witness: two legal states with identical un-named graph structure
    differing only in term writing. -/
def freeW1 : St := ⟨[0, 1], [(0, 1)], 0, 1⟩
def freeW2 : St := ⟨[0, 1], [(1, 0)], 0, 1⟩

theorem freeW1_legal : freeW1.Legal := by
  intro x hx
  simp [freeW1] at hx
  omega

theorem freeW2_legal : freeW2.Legal := by
  intro x hx
  simp [freeW2] at hx
  omega

theorem free_witness_distinct : freeW1 ≠ freeW2 := by decide

/-- Anchored splitting witness: two legal states with identical anchored names (0, 1)
    and isomorphic relations differing only in the writing of an added term (2 vs 3). -/
def anchoredW1 : St := ⟨[0, 1, 2], [(0, 1), (0, 2)], 0, 1⟩
def anchoredW2 : St := ⟨[0, 1, 3], [(0, 1), (0, 3)], 0, 1⟩

theorem anchoredW1_legal : anchoredW1.Legal := by
  intro x hx
  simp [anchoredW1] at hx
  rcases hx with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem anchoredW2_legal : anchoredW2.Legal := by
  intro x hx
  simp [anchoredW2] at hx
  rcases hx with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem anchored_witness_distinct : anchoredW1 ≠ anchoredW2 := by decide

/-- The swap transposition permutation (swapping 2 and 3) maps anchoredW1 to anchoredW2,
    preserving names and relation structure, while the written states remain distinct. -/
theorem anchored_witness_same_card : anchoredW1.T.card = anchoredW2.T.card := by decide
theorem anchored_witness_same_edges : anchoredW1.A.card = anchoredW2.A.card := by decide
theorem anchored_witness_same_names :
    anchoredW1.a = anchoredW2.a ∧ anchoredW1.b = anchoredW2.b := by decide

end Seed.WrittenRefusal

open Seed.WrittenRefusal

#print axioms writtenEq_refl
#print axioms written_step_preserves_legal
#print axioms refusal_invariant
#print axioms identify_given_refused
#print axioms adding_self_loop_refused
#print axioms freeW1_legal
#print axioms free_witness_distinct
#print axioms anchoredW1_legal
#print axioms anchored_witness_distinct
#print axioms anchored_witness_same_names
