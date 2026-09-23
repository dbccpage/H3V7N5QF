# Change log

1. Plan and stopping conditions recorded in `CLAUDE.md` before the rest
   (`d12b0f0`).
2. The written exploration, the count of writings, the comparison with the
   base's least writing, the Lean witness that the swap is a different
   state, and the paper. The bound 3 terms and 12 rounds is past the last
   new result. O1 and O2 stay open.
3. **Review repair.** `writings_called_the_same` compared `same_written` (which
   is `==`) with `!=` of the same two states, so it could not fire on the real
   code; it now compares `same_written` with the written key over every pair
   of reached states. The evidence recorded only how many rounds differ from
   the base count, while the paper said the rounds are never shorter and
   exceed it by at most 2 and 4; `rounds_below_the_base_cost` (a disagreement
   field, with a bite case) and `greatest_excess_over_the_base_cost` now record
   both, and `rounds_off_the_base_cost` became `rounds_above_the_base_cost`.
   The literal `letter_supply_unbounded_for_a_positive_term_count: true` was
   replaced by a computed `sample_letter_supply_grows` and the argument in
   section 4. D1 was marked derived for what is the chosen sameness (C1); it
   now claims only the computed `n!` split. O2 is closed for the named reading
   by D3 and the base's `fewest_changes_lower_A`, `_B`, which bound every
   sequence whatever the number of terms; it stays open without the names.
   The base theorems cited in re-checks are printed in the axiom report.
   `tests/test_eighteenth_leanreport.py` covers `code/eighteenth/leanreport.py`.
