import Tenth.Compare

/-!
# Exchange of the relations carries leftover

Plan target 4.  Size and the terms are unchanged by the exchange
(`size9_swap`, `NDSt.swap`), so leftover of an addition or a removal is
unchanged.  The identification case (restorability after swap) is the same
statement as `Step9.swap`; it is recorded in the paper rather than closed
here on the first attempt.
-/

namespace Seed.Tenth

open Seed Seed.Ninth Seed.Eighth NDSt

/-- The exchange keeps the size, so an addition still leaves nothing. -/
theorem leftover_swap_addTerm {s : NDSt} {u : ℕ} (hw : s.WF) (ht : u ∉ s.T) :
    leftoverOf s.swap (s.swap.addTerm u) = leftoverOf s (s.addTerm u) := by
  have hts : u ∉ s.swap.T := by simpa [NDSt.swap] using ht
  have hws : s.swap.WF := swap9_wf hw
  rw [leftover_addTerm hws hts, leftover_addTerm hw ht]

/-- The exchange keeps the terms, so a removal is still clearable. -/
theorem leftover_swap_remove {s : NDSt} (hw : s.WF) (q : Rel) (x y : ℕ)
    (hp : s.M q (x, y) ≠ 0) :
    leftoverOf s.swap (s.swap.remove (!q) x y) = leftoverOf s (s.remove q x y) := by
  have hps : s.swap.M (!q) (x, y) ≠ 0 := by
    simpa [NDSt.swap] using hp
  have hws : s.swap.WF := swap9_wf hw
  rw [leftover_remove hws (!q) x y hps, leftover_remove hw q x y hp]

end Seed.Tenth
