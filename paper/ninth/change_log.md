# Change log, ninth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-ninth-derivation` (the extra worktree of this repository in which
the third to eighth derivations were made; Phase 0 of the ninth is committed
at aceb154).

1. **`CLAUDE.md` gained the ninth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/ninth/prompt.md`. The earlier plans above it are unchanged.

2. **Lean: a ninth library `Ninth` in the same Lake package, importing
   `Eighth`; the lakefile gained the target (recorded in
   `paper/change_log.md`, item 27).** The plan's targets 1–5 all closed on
   the first compile, target 5 (rewriting, the every-writing statement)
   included. Written afresh without names: the two-relation state `NDSt`,
   the empty beginning, the exchange of the two relations, the four maps
   (`DSt.forget`, `NDSt.name`, `NDSt.proj`, `NSt.ofR`) and their
   commutations with the operations, `Step9` / `Reach9`, the size as the
   cost (`fewest_changes9`, `cost_adds_up9`, `cost_not_sum_of_parts9`),
   the has-a-term criterion (`reach9_iff`, `results_pair9`), the comparison
   with the seventh and the eighth, and rewriting (`rename9`,
   `fewest_changes9_every_writing`). Reused through the maps: the eighth's
   `reach8_raise`, `reach8_of_names`, `cycle2_8` and rename lemmas, the
   seventh's well-formedness of a change, its size lemmas, its criterion,
   and the fifth's total lemmas on a part. Nothing in an earlier library
   body was modified.

3. **Layout: a new package `code/ninth/` importing from the earlier
   packages only what the empty beginning and the second relation leave
   intact; no earlier module is modified.** Reason: the task allows changes
   to the earlier derivations' files only to correct a defect, and none was
   found. Imported: the eighth's two-relation state with `names = None`, its
   sameness under any rewriting acting on both relations, `canonical`,
   `rewrite`, `of_r`, `remove`, `identify`, the change record with a
   relation, the four kinds, the list of changes and `perform`,
   `attempt_counts`, the two-change cycle, `count_free` and `product_count`,
   the seventh's single-relation count, the unnamed statements, the writers,
   the Lean report runner, and the seventh's and eighth's explorations for
   the comparison. Defined afresh: the empty beginning, the exchange of the
   two relations, the exploration from an empty two-relation state, the cost
   as the size (and the comparison with the sum of the parts' seventh
   costs), the has-a-term criterion, the one-term binomial, the two-term
   closed form with eight multiplicities, the count of results whose
   relations agree, and the comparisons with the seventh (nothing in `s`,
   and by the exchange nothing in `r`) and with the eighth (names
   forgotten).

4. **One beginning and one reading of sameness.** Reason: the seed gives
   nothing (no `bra` alternative, no names), and with no names the
   rewritings keeping the names are all rewritings (D12), so the two
   readings coincide; every exploration is run once instead of the eighth's
   four times.

5. **The comparison with the eighth runs the eighth's explorations four
   rounds fewer than the ninth's, from both its beginnings under both its
   readings.** Reason: an eighth result's size is at most its eighth-seed
   cost plus four, so every eighth result then lies within the ninth's
   rounds; the results with a term whose eighth-seed cost is within the
   eighth's rounds must be exactly the eighth's results, each at the round
   its cost formula gives, and the named results with their names forgotten
   must be results here. Both halves are checked on every run and the
   census. The comparison with the seventh runs at the same bound and
   rounds: the results asserting nothing with `s` (and those asserting
   nothing with `r`) must be the seventh's, at the same rounds, with the
   same shortest-sequence counts.

6. **The cost is recorded as the size, and beside it the seventh's cost of
   each part.** Reason: the eighth's "cost is a sum" is true of the two
   totals and false of the terms, which a per-relation cost counts twice
   (`cost_not_sum_of_parts9`; `sum_of_the_part_costs_exceeds_the_cost_by_the_terms`
   in every run). The paper must not state 8:D4 as `cost₇(r) + cost₇(s)`.

7. **Bounds: the plan's targets completed here and are the bounds used.**
   5 terms with 8 rounds, 3 terms with 9, 2 terms with 12, a census at 6
   terms with 8 rounds, full logs at 2 terms and 3 rounds, reachability at
   3 terms and 5 rounds along 7. The independent count sized the runs in
   advance; no lowering was needed.

8. **Tests `tests/test_ninth_*.py` on the seventh/eighth pattern**, including
   `write_all` on a SMALL plan and an injection test for every disagreement
   branch of `code/ninth/evidence.py`. Reason: the coverage gate fails an
   evidence module that is not fully covered.

9. **Evidence written by `python code/generate_ninth.py`**, hashed
   (`evidence/ninth/MANIFEST.sha256`); `--check` regenerates into a
   temporary folder and compares. The axiom report by
   `python code/lean_report_ninth.py`. Completeness within the bound is the
   independent count; the frontier is exported exactly.

10. **Paper, claim ledger, this change log.** Every notion one source
    status; the ledger re-check column says whether each cited claim
    survives with nothing given and two relations. The task's question is
    answered in `paper.md` §0 and §7: 7:D4, 7:D8, 7:D12 hold; 8:D5 holds
    (empty included); 8:D4 holds as `size = cost₇(r) + Σ s`, not as a sum of
    two seventh costs; 8:D10 holds for `n ≥ 2`. Interferences: shared terms,
    shared rewriting, `C(p+q, p)` interleaving, exchange symmetry. Outside
    names only in the paper's final section.

11. **`python code/generate_ninth.py --check` matched** a fresh regeneration
    of `evidence/ninth/` (every run's checks pass; 10 416 / 25 965 / 22 021
    results in the three explorations, 10 458 in the census). The prose
    watchlist is clean on the tracked tree. The ninth paper's three watched
    hits (one enumeration term, two algorithm terms) are all in §10; pinning
    `paper/ninth/paper.md` in `ci/prose_watchlist.json` is needed once that
    file is tracked, and that JSON is not an owned prefix of this lane.

12. **Repair: ledger and paper matched the Lean and computed evidence.**
    D3's change-count formula is paper + computed, not Lean (`Step9.proj` is
    not a count; O3 lists it). D13's 5-term comparison uses the 10 415
    results with a term (1 762 / 8 645 / 8 with `bra`; 0 / 10 407 / 8
    without). 8:D13 is re-checked in two clauses: `asb`/`arb` without
    object; `s_costs_its_total` survives jointly as `Σ s` (D4).
    `Step9.lowers_or_adds` and `s_costs_its_total` are in the axiom report.
    K10 no longer claims a pin that the unowned watchlist JSON does not
    have. The eight earlier `--check`s and Lean reports were re-run and
    matched (`paper/change_log.md` item 27).

13. **The prose watchlist baseline was re-pinned for `paper/ninth/paper.md`.**
    Three watched hits (one enumeration term, two algorithm terms), all in
    §10. Reason: AA8; the paper is now tracked.

## Whole-repo review repairs (2026-09-23)

- F002: printed seven cited Eighth theorems and the cited Fifth containment witness, then regenerated the Lean report and manifest. F013: filled O5 carry-forward evidence. No claim or theorem statement changed.
