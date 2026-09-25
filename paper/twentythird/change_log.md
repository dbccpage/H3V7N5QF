# Change log, twenty-third derivation

Each material change, and its reason. Newest last. Commits are on the branch
`derivation/twentythird`; nothing is pushed.

1. **The run first stopped at a blocker, before any work.** At the start of the
   session every write (even to `CLAUDE.md`) and every `python` or `lake` call
   was refused by the session's permissions (the read-block setting asks the
   person for any command it cannot analyse, and no approval could be given),
   so the plan could not be written. Following the blocker rule of `CLAUDE.md`,
   the run stopped and reported it. The operator then allowed writes, `python`
   and `lake`, and the run resumed from Phase 0. Nothing was written or
   committed before that.

2. **`CLAUDE.md` gained the twenty-third derivation's plan and stopping
   conditions (AL1–AL10), committed alone before any other work.** Reason:
   required by `prompt/twentythird/prompt.md`. The plan's text was checked
   against the prose watchlist (`--probe`) before it was written, since
   `CLAUDE.md` carries no pinned hit.

3. **Layout: a new package `code/twentythird/`, launchers
   `code/run_twentythird.py` and `code/lean_report_twentythird.py`; no earlier
   module is modified.** Imported: the twenty-second's state, `excess`,
   `plain`, its result (`plain_result`) and cost (`plain_cost`), its exploration,
   shortest-sequence counts and reachability graph (run as they stand, reading
   C-E), `ofR` and the seventh's state, `key_j2`, its Lean report helpers; the
   ninth's exploration (C-E′) and statements; the seventh's exploration;
   `fourth.state._rewritings`; the writers and `compare_evidence`. Defined
   afresh: raising, the mark of a result (`result_key`), the sums kept by the
   sameness and the certificate, the cost by raising sets of terms (`descend`,
   `least_tables`, `search_fewest`, the closed forms), the states asserting the
   fewest, the grouping of the exploration, the counts, the witnesses and the
   map back, the readings, the statements with a third verdict, and the checks
   (`RaisingCheck`, eighteen disagreement lists).

4. **A first version of the respect check compared outcomes of one change
   performed on the states of a result as they are written — each is its own
   least writing, so term `0` of one is not term `0` of another — and reported
   600 disagreements that were not there.** The states are now rewritten onto
   the representative's writing first (`align`); the check is clean.

5. **`ci/check_mutation_bite.py` gained a twenty-third panel (eighteen bite
   cases, one per field of `RaisingCheck`).** Reason: required by the task; each
   case perturbs one function in `twentythird.evidence`'s namespace and the
   field it guards fires.

6. **`ci/check_axiom_citations.py` lists the twenty-third derivation.** Reason:
   so its citations of `lean4_core/Twentythird` theorems are checked against
   its own report.

7. **Lean: a library `Twentythird` in the existing package `lean4_core/`; the
   lakefile gains it as a library and a default target** (recorded in
   `paper/twentysecond/change_log.md` item 14, the lakefile being the
   twenty-second's file). Reason: required by the task.

8. **Lean: `omega` brings in `Classical.choice` when it proves a conjunction,
   or when a negated conjunction is in its context** (probed with
   `#print axioms` on small test theorems). The first build of `Raise.lean` and
   `Cost.lean` depended on it through `by_cases` on conjunctions and
   `show … ∧ … by omega`. Every such proof was rewritten to split on single
   conditions and build conjunctions by hand (`ite_iff`), and negated
   conjunctions are passed to `if_neg` inline rather than left in context. The
   report now lists every theorem within `propext` and `Quot.sound`. Also:
   `omega` with many `natAbs` terms at once timed out; the triangle
   inequalities are now separate small lemmas (`natAbs_add2`, `natAbs_add3`,
   `sum_nine_ge`).

9. **Lean target 7 (rewriting and the full sameness) closed on the single
   attempt** (`genW3_iff_sameW3`, `cost3_every_writing`, `sameW3_nothing_iff`).
   Added beyond the plan: `merge_loses3`, `two_additions_undo3`; and, at the
   first review of the paper, `readBack3_self_iff` and `readBack3_answer_cost`,
   so that what the map back returns on a mapped state is stated in Lean and not
   only shown on examples (152 theorems in all).

10. **Bounds.** The twenty-second's own bounds were used (5 terms and 8 rounds,
    3 and 10, 2 and 24; the ninth's explorations at 8, 9 and 12 rounds); every
    run completed in about a minute here. The listing counts for four and five
    terms (`listing_counts`) are the slowest part.

11. **Statements.** The twenty-second read its statements on the plain state,
    one per result; here a result has several states asserting the fewest, so a
    third verdict, "depends on the state", was added rather than choosing one
    state (`follows.py`).

12. **Every earlier derivation's evidence was re-checked with its `--check`
    after this derivation's code was in place**
    (`research/twentythird/check_earlier.py`): all twenty-three derivations,
    this one included, regenerate byte-identically (`failed: 0`). The gates of
    "Done" were run in the foreground after the last change: `python -m pytest`
    (1 049 passed), `python code/xry/gate.py coverage.json` (line 99.81 %,
    branch 99.66 %, every evidence module fully covered), `python -m mypy`, the
    prose watchlist, `ci/check_vacuous_checks.py`,
    `ci/check_definitional_citations.py`, `ci/check_mutation_bite.py`,
    `ci/check_axiom_citations.py`, and
    `lake +leanprover/lean4:v4.33.1 -d lean4_core build` (exit code 0).
