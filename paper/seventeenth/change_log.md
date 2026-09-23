# Change log

1. Plan and stopping conditions recorded in `CLAUDE.md` before other work
   (the prompt requires that commit on its own).
2. Reading of the seed against the base, in `research/seventeenth/`. Not
   evidence. Two readings of an obstructed change (enter it, or not) and
   two readings of "makes some `xrx`" are kept.
3. `code/seventeenth/` computes both readings. At 3 terms and 6 rounds the
   A-replace closure matches `xry.explore` and the base cost, and no result
   asserts `xrx`. The A-perform closure does: identifying `a` with `b` is
   one change whose outcome asserts `ara`, and the base cost of that outcome
   is greater than 1. A refusal changes nothing. Remove-then-identify and
   identify-then-remove end at the same state.

cycle: landed the 17–21 seeds on main (PR #38); wrote the plan, the reading, and the two explorations with their checks; next Lean (`LoopFree`, the embedding of the base `Step`, the A-perform witness) and the paper.
