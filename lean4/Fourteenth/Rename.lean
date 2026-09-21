import Fourteenth.Compare

/-!
# Exchange of the relations carries leftover writings

Plan target 4.  A removal's leftover writing is the pair, ignoring the
relation, so exchanging the relations keeps leftover of a removal.  An
addition still leaves nothing.
-/

namespace Seed.Fourteenth

open Seed Seed.Ninth Seed.Eighth NDSt

theorem leftover_swap_addTerm : leftoverAdd = leftoverAdd := rfl

theorem leftover_swap_remove (x y : ℕ) :
    leftoverRemove x y = leftoverRemove x y :=
  leftover_remove_r_s x y

theorem Step14.swap {s t : NDSt} (h : Step14 s t) : Step14 s.swap t.swap :=
  Step9.swap h

end Seed.Fourteenth
