import H3V7N5QF.Finite

/-!
# Loop-freeness is a predicate, not a given

The seed strikes "for no term `x` may `xrx` be asserted". `LoopFree` is the
base's `Legal`, kept as a predicate. `HasXrx` is its negation.
-/

namespace Seed.Seventeenth

open Seed

/-- No `xrx` is asserted. The base's `Legal`, no longer a given. -/
abbrev LoopFree (s : St) : Prop := s.Legal

/-- Some `xrx` is asserted. -/
def HasXrx (s : St) : Prop := ∃ x, (x, x) ∈ s.A

theorem hasXrx_iff_not_legal (s : St) : HasXrx s ↔ ¬ s.Legal := by
  constructor
  · rintro ⟨x, hx⟩ h
    exact h x hx
  · intro h
    by_contra hempty
    apply h
    intro x hx
    exact hempty ⟨x, hx⟩

theorem hasXrx_iff_not_loopFree (s : St) : HasXrx s ↔ ¬ LoopFree s :=
  hasXrx_iff_not_legal s

/-- A state that already asserts `0r0`, used to separate the two readings of
"makes some `xrx`". Terms `0, 1, 2`; nothing between `1` and `2`. -/
def loopyWitness : St := ⟨{0, 1, 2}, {(0, 0)}, 0, 1⟩

theorem loopyWitness_hasXrx : HasXrx loopyWitness :=
  ⟨0, by simp [loopyWitness]⟩

theorem loopyWitness_not_loopFree : ¬ LoopFree loopyWitness :=
  (hasXrx_iff_not_loopFree _).1 loopyWitness_hasXrx

end Seed.Seventeenth
