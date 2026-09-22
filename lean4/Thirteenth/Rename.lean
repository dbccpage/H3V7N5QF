import Thirteenth.Compare

/-!
# Exchange of the relations keeps the coarser writing

Plan target 4.  The coarser writing is the sum of the two multiplicities, so
exchanging the relations does not change it.  A change of the thirteenth seed
exchanges with the ninth's `Step9.swap`.
-/

namespace Seed.Thirteenth

open Seed Seed.Ninth Seed.Eighth NDSt

theorem Step13.swap {s t : NDSt} (h : Step13 s t) : Step13 s.swap t.swap :=
  Step9.swap h

theorem coarse_swap' (s : NDSt) : coarse s.swap = coarse s :=
  coarse_swap s

end Seed.Thirteenth
