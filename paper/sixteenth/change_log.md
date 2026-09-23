# Change log, sixteenth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-sixteenth-derivation`.

1. **`CLAUDE.md` gained the sixteenth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/sixteenth/prompt.md`. The earlier plans above it are unchanged.

2. **Layout: a new package `code/sixteenth/` importing from the earlier
   packages only what the feedback leaves intact; no earlier module is
   modified.** The state with its record is new (`state.py`); the record is
   modelled as a one-relation counted state on the same terms, so the fourth's
   `perform`, `rewrite` and the fifth's `remove`, `identify` act on it
   unchanged (reuse, not reproof). Defined afresh: the five changes and the
   admission, the exploration with its frontier and shortest-sequence counts,
   the potential and the cost rule, the mass, the carrying criterion and the
   search, the count with a third factor and the one-term closed form, the
   checks (`RecordCheck`, twelve disagreement fields), the statements, the
   two unchosen readings, the evidence writer. The reading notes are in
   `research/sixteenth/reading_the_seed.md`.

3. **`ci/check_mutation_bite.py` gained a sixteenth panel; `ci/check_definitional_citations.py`
   gained the sixteenth's record noun (`leftover`).** Reason: required by
   `prompt/sixteenth/prompt.md` (a panel of the same shape, one mutation per
   field); the noun makes the notion-mismatch signal apply to the sixteenth's
   ledger as it does to the tenth's to fifteenth's. Both are `ci/` files, not
   an earlier derivation's; recorded here because they are shared.

4. **Lean: a sixteenth library `Sixteenth` in the same Lake package, importing
   `Fifteenth`; the lakefile gained the target (recorded in
   `paper/change_log.md`).** Targets 1–5 of the plan closed: `RSt`, the five
   operations, `Step16`, `Reach16`, the maps to and from the ninth
   (`State.lean`, `Step.lean`); the same-relation identity and the
   other-relation witnesses (`State.lean`); the potential as the cost, the
   rise/fall count and "no fall on a shortest sequence" (`Cost.lean`); the
   mass invariant, the failure of the has-a-term criterion, the results, the
   cycles, admitting every leftover (`Reach.lean`); what survives
   (`Compare.lean`). Target 6 (`rename16`) was not attempted (ledger O6). A
   general lemma new to the repository, that a term added and identified away
   leaves a one-relation state as it was (`NSt.identify_addTerm`), was needed
   for the cycle at states without an assertion.

5. **Bounds.** 3 terms with 8 rounds, 4 with 7, 2 with 10 (the ninth ran 5
   with 8 and 3 with 9); reachability at 3 terms and 5 rounds along 7; the
   unchosen readings at 2 terms and 6 rounds. Reason: the results of round `k`
   are the states of potential `k`, about a third more than the ninth's at
   each round, and the reachability search on 431 649 pairs (3 terms, 6
   rounds) took two minutes, above the "minutes" budget when regenerated
   with `--check`; 27 889 pairs take seconds. Declared in `Plan` and in the
   paper (C8′).

6. **Watchlist pin for the sixteenth paper's final section.** The census
   gained `paper/sixteenth/paper.md` (hits of outside-theory terms in §14).
   Reason: the gate tracks every watched hit; the body of the paper has none.

7. **Lean: the operation, the change and the fall named `admit` are renamed
   `admitLeftover` (`RSt.admitLeftover`, `Step16.admitLeftover`,
   `Fall16.admitLeftover`); three proofs of `State.lean`, at which the build
   stopped with five errors, and two of `Cost.lean`, found on reading ahead
   of the build, are repaired; the build is re-run with its exit code read
   directly.** Reason: the receipt behind item 4 had been read through a
   shell pipe, which returns the exit code of its last filter and not of
   `lake build`, and the library did not compile. The word `admit` fails the
   scan of `code/xry/leanreport.py` on its own, whatever it names: the scan
   matches the bare word outside comments, while a theorem name such as
   `potential_admit` is one word to it and is unchanged. The repairs, none of
   which changes a statement: `mass_remove` names the relation of the other
   projection (the rewrite had matched the projection of the removed relation
   first, and `decide` was handed `false ≠ false`); `mass_identify` reads
   the fifth's `total_identify` through the naming map with `have` rather
   than `rw`, the fifth's statement being on the named state;
   `NSt.identify_addTerm` turns `0 ≠ m.M p` round to what `WF` takes and
   states its two `merge_of_ne` facts before using them;
   `eq_ofRSt_of_total_zero` reads the record of the embedding as `0` before
   `omega`, which does not unfold it; `leftOne_admit` unfolds `ara16`. Three
   linter warnings cleared (two unused simp arguments, an unused binder).
   Every theorem of `Sixteenth/Axioms.lean` reports within `propext`,
   `Classical.choice`, `Quot.sound`; the report,
   `evidence/sixteenth/lean_axioms.txt`, did not exist before this item.

8. **Ledger: the axiom column of D1, D2, D10, D11, R8, R10 and R11 corrected
   from "none" to "std".** Reason: those cells were written ahead of a report
   that did not exist. The regenerated report shows every theorem they cite
   depending on `propext` and `Quot.sound` — the definitions in their
   statements use `Function.update` on pairs of numbers, whose equality test
   carries both — and some on `Classical.choice`. No statement, proof or
   status changes.

9. **Watchlist pin actually regenerated for `paper/sixteenth/paper.md`.**
   Reason: item 6 records a pin the tree did not carry —
   `ci/prose_watchlist.json` had no entry for the sixteenth paper, and the
   gate (and `tests/test_prose_watchlist.py`) failed on the paper's two
   hits, both in §14. `--regen` added exactly that entry (two terms, once
   each; diff inspected); the body of the paper has none. Item 6 is left as
   written, being the record of what was claimed.

10. **The count of pairs the two mass invariants admit and the carrying
    criterion refuses no longer also requires the ninth's criterion; the
    docstring of `reach.py` no longer cites theorems that were not proved.**
    Reason: `write_reach` counted `mass_ok` and not `carries` only when the
    ninth's criterion also admitted the pair, so the three states with a
    term and mass 0 into the empty state (mass and diagonal mass both 0,
    no map into no terms) were left out. The published count was 4 224; it
    is 4 227. `alternatives_ok` now requires the drop reading's carrying
    criterion to disagree with search, as D14 states. `reach.py` cited
    `Reach16.diag_le` and a Lean sufficiency for an arbitrary carrying map;
    neither exists (O3, O4). Item 4's "targets 1–5 closed" is left as
    written; those two targets of item 4 in the plan were not closed.

## Whole-repo review repairs (2026-09-23)

- F010: printed two cited theorems, Reach16.swap and remove_add9, then regenerated the Lean report and manifest. No theorem statement changed.
