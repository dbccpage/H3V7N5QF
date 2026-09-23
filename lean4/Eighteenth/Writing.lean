import H3V7N5QF.Cost

/-!
# A writing is the result

The base records that a state written otherwise than `a = 0`, `b = 1` is the
same result under a rewriting, and does not formalise that step. Here three
writings of two terms are pairwise distinct: what is given (`arb`, names on
`0` and `1`), the assertion `bra` with those names unmoved, and the assertion
`bra` with the names exchanged. The Python `rewrite` by the transposition
`(1, 0)` produces the third of these.
-/

namespace Seed.Eighteenth

open St

/-- `bra` asserted, names still on `0` and `1`. -/
def braWritten : St := ⟨{0, 1}, {(1, 0)}, 0, 1⟩

/-- `bra` asserted, and the names exchanged. -/
def swappedGiven : St := ⟨{0, 1}, {(1, 0)}, 1, 0⟩

theorem given_ne_bra : givenA ≠ braWritten := by decide

theorem swapped_ne_given : swappedGiven ≠ givenA := by decide

theorem swapped_ne_bra : swappedGiven ≠ braWritten := by decide

end Seed.Eighteenth
