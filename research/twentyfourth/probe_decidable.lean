def probe1 (n : Nat) (p : Nat → Prop) [DecidablePred p] : Decidable (∃ x, x < n ∧ p x) := inferInstance
def probe2 (n : Nat) (p : Nat → Prop) [DecidablePred p] : Decidable (∀ x, x < n → p x) := inferInstance
theorem probe3 (n : Nat) (f : Nat → Int) : (∃ x, x < n ∧ f x ≠ 0) ∨ ∀ x, x < n → f x = 0 := by
  by_cases h : ∃ x, x < n ∧ f x ≠ 0
  · exact Or.inl h
  · exact Or.inr (fun x hx => by
      by_cases e : f x = 0
      · exact e
      · exact absurd ⟨x, hx, e⟩ h)
#print axioms probe1
#print axioms probe3
