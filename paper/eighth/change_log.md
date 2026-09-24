# Change log, eighth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`worktree-eighth-derivation`, made from the last commit of the seventh
derivation on `worktree-third-derivation` (whose pull request was still open,
so the eighth's pull request is opened against that branch); the worktree is
the one in which the third to seventh derivations were made.

1. **`CLAUDE.md` gained the eighth derivation's plan and stopping conditions,
   committed before any other work.** Reason: required by
   `prompt/eighth/prompt.md`. The earlier plans above it are unchanged.

2. **The state model is new: `DState` (Python), `DSt` (Lean) — terms, a
   multiplicity for each ordered pair in each of the two relations, the
   names.** Reason: the seed adds a second multiplicity function on the same
   terms. Its two *parts* (the `r` part, the `s` part) are each a state of
   the sixth seed with the same terms and names (`fourth.state.MState`; Lean
   `DSt.proj`), and a state of the sixth is a two-relation state asserting
   nothing with `s` (`of_r`; Lean `MSt.ofR`). In Lean the multiplicity
   function is indexed by a relation tag (`Rel := Bool`), so that every lemma
   about one relation is stated once and the two projections are one
   definition; the operations commute with the projections definitionally or
   by one `Function.update` lemma each.

3. **Layout: a new package `code/eighth/` importing from the earlier
   packages only what one relation leaves intact, applied to a part; no
   earlier module is modified.** Reason: the task allows changes to the
   earlier derivations' files only to correct a defect, and none was found.
   Imported and applied to a part: the fourth's `perform` for a term and an
   assertion, the fifth's `remove` and `identify`, the sixth's `cost`,
   `cost_free_by_placement`, `lost`, `lost_free`, `merged_optimal`,
   `raises_by_one`, `attempt_counts` (the loop-making count), `reachable`,
   the statements tested (`fourth.follows`, `fifth.follows`, `sixth.follows`,
   with the wording rewritten for `s`), `fewest_classes`, and the sixth's
   orbit helpers (`_unchanged`, `_with_diagonal`, `_shifted`, `_exactly`,
   `_at_least`, `_averaged`, the kinds, `lost_of_kind`); imported as they
   are: `Kind`, `Sameness`, the rewritings of `fourth.state`, `series`, the
   cycle machinery, the writers, `compare_evidence`, the Lean report runner,
   and the sixth's exploration and sequence counts for the comparison.
   Defined afresh: the two-relation state and its sameness (a rewriting acts
   on both relations at once), the change record with a relation, the list
   of changes, the exploration, the two-change cycle, the cost as the sixth's
   on the `r` part plus the `s` total, the cost-raising rule for `s`
   changes, the independent count with two multiplicities per cycle, the
   product of the single-relation counts, the two-term closed forms with the
   `s` states convolved in, the joint statements, the invariants per
   relation, and the comparison with the sixth on the results asserting
   nothing with `s`.

4. **What is given asserts nothing with `s` (C2″).** Reason: the seed flags
   "anything written with `s`" as not given, as it flags `bra`; unlike `bra`
   the candidates are infinitely many, every one a result of the chosen
   beginning reaching the same results (D5, D8). They are kept as
   alternatives whose cost formula the paper proves (C2″) and does not
   compute (O4).

5. **The order of the changes of a result puts the removals of `r` before
   those of `s`, and the additions of `r` before those of `s` (C6).** Reason:
   the seed's order of kinds among equals, and the seed's order of the
   relations (`xry` or `xsy`); the order cannot move a result to another
   round (D4).

6. **The comparison with the sixth requires equality of results, rounds and
   shortest-sequence counts on every result asserting nothing with `s`.**
   Reason: a shortest sequence to such a result never touches `s` (an `s`
   addition would need an `s` removal, which is not cost-raising), so the
   counts must agree exactly — no "names apart" split as the sixth had
   against the fifth. Checked on every run and census.

7. **The independent count multiplies every inner polynomial of the sixth's
   named and free counts by the `s` factor of the same rewriting (the free
   series over all its cycles), and records beside it the product of the
   single-relation counts.** Reason: a rewriting fixes a two-relation state
   exactly when it fixes both parts, so the orbit count is the average of
   products, not the product of averages; the computed departure from the
   product (8 against 4 with two terms and one assertion in each relation)
   is the precise sense in which `s` is not an independent copy (D10). The
   sixth's helper `_at_least` needs a degree of at least two, which the
   tests respect.

8. **Lean: an eighth library `Eighth` in the same Lake package, importing
   `Seventh`; the lakefile gained the target (recorded in
   `paper/change_log.md`, item 26).** The plan's targets 1–5 all closed,
   target 5 (rewriting, the every-writing statements) included; six proofs
   needed a second compile (a projection lemma applied to the wrong state, a
   cast, an `omega` that wanted the split lemma first, an argument order in
   `reach8_raise`, and two `Function.update` rewrites better left to `simp`).
   An unused helper (`total_proj_other`) whose case split failed was
   dropped in favour of `Step8.split`. Reused on a part: the sixth's
   `Step6.wf`, `Step6.nonempty`, `Step6.names_stay_merged`, `Step6.costA_le`,
   `Step6.size_step`, `fewest_changes6_A`, `_B`, `reach6_of_names`,
   `reach6_iff`, `result6_iff_A`, `costA6_rename`; through the embedding:
   `no_return_fails6`, the fifth's `antisymm_fails`; the fourth's and
   fifth's total and rename lemmas. Written afresh: the two-relation state
   and its projections, the raising path with a relation tag, the clearing
   of `s`, `remove_addAssertion` (the two-change cycle), and the comparison.

9. **Bounds sized by the independent count before any run.** A result has
   `2n²` pairs to assert, so the results per round grow much faster than the
   sixth's: 4 terms (FREE) or 3 terms (ANCHORED) with 5 rounds hold 8 109 /
   7 639 and 10 404 / 12 123 results, 3 terms with 6 rounds 22 435 / 23 171
   and 44 843 / 52 849, 2 terms with 8 rounds 10 581 / 11 049 and 20 140 /
   24 832; at 7 rounds the main runs would hold 187 042 to 485 894 results
   each. The plan's targets (7 rounds; 20 two-term rounds) were lowered to
   these before the first run, for size, not time; reachability is tested
   at 2 terms and 4 rounds (about half a million ordered pairs with the
   names kept), where 3 terms would give millions.

10. **Slips found by the tests during the run, all in the eighth's own test
    files, none in the derivation's code.** Numbers guessed before the
    evidence existed (a cost with `bra` given, a census count of results
    asserting nothing with `s`, the round in which the two relations first
    agree, the number of statements tested, a lowered fewest-classes count,
    a capped orbit count) were corrected to the computed values; one
    assertion was stated for the wrong reading of sameness; one compared a
    summary value with an integer under `mypy --strict`. No evidence had
    been written.

11. **Review pass over paper and ledger after the first draft.** The
    numbers of §6 were filled in from the final evidence; the wording of
    D12 (the interaction) was tightened; ten theorems the ledger cites
    (`givenA8_a`, `givenA8_b`, `givenB8_a`, `givenB8_b`, `givenA8_proj`,
    `not_ne`, the first library's `bra_not_derived`, `bra_not_refuted`, the
    fifth's `contains_fails`, `reach5_clear`) were added to
    `Eighth/Axioms.lean` and the axiom report rewritten (140 theorems). No
    claim or status changed.

12. **Re-runs of the earlier derivations' checks.** After this work the seven
    earlier `--check`s (`python code/generate.py --check`, `_second`,
    `_third`, `_fourth`, `_fifth`, `_sixth`, `_seventh`) and the seven earlier
    Lean reports were re-run; their outcomes are recorded here once known
    (item 13).

13. **Outcome of the re-runs (item 12).** `python code/generate.py --check`,
    `python code/generate_second.py --check`, `python code/generate_third.py
    --check`, `python code/generate_fourth.py --check`, `python
    code/generate_fifth.py --check`, `python code/generate_sixth.py --check`
    and `python code/generate_seventh.py --check` each reported a match with
    a fresh regeneration (64, 278, 304, 166, 522, 840 and 847 seconds here,
    beside other runs); `python code/lean_report.py`, `_second`, `_third`,
    `_fourth`, `_fifth`, `_sixth` and `_seventh` each built all eight
    libraries and rewrote their `lean_axioms.txt` and manifest
    byte-identically (`git status` shows no change under `evidence/`,
    `evidence/second/`, `evidence/third/`, `evidence/fourth/`,
    `evidence/fifth/`, `evidence/sixth/` or `evidence/seventh/`). So the
    evidence of all seven earlier derivations still regenerates. The
    eighth's own `python code/generate_eighth.py --check` matched (1 067
    seconds, beside other runs), after `python code/generate_eighth.py`
    (1 032 seconds) and `python code/lean_report_eighth.py`.

14. **Phase 6 repair of ledger/paper mismatches (no code, no evidence).**
    §0 now lists D3 and D4(iv) among the derived claims proved in the paper
    and checked by computation only, matching O3. D3 no longer cites
    `Step8.proj` as Lean evidence for the change-count (that theorem splits
    a change onto a part; the count is `attempts_equal_formula`). R1 axioms
    are `std`, matching `givenA8_a` / `givenA8_b`. R2 cites
    `given.json` (`of_which_obstructed`) and `summary.json`
    (`given.attempts_not_performed`). Chosen C1′ re-checks 4:C1′ on a part.
    C10, N4, N5, N7, N8 re-check cells now say jointly, on a part, or
    through the embedding. Findings and Lean are unchanged. Committed
    from `main`; `prompt/` unchanged.

## Whole-repo review repairs (2026-09-23)

- F008: printed the cited sixth upper-bound theorem and regenerated the Lean report and manifest. F011: relation attempt counts now come from the change list, with an injected list-drift test; regenerated evidence. F013: filled O5 carry-forward evidence. No claim or theorem statement changed.
