# Fenced correspondence audit and ten blind-seed proposals

## Scope

The proposal work was authored independently from plan-only commit
`8f2c5179159b7dbdb9db06d39c47cb084abddb0f`. After repair PR #43
merged, this branch integrated the new `main` and retained both entries in
`paper/change_log.md`. Against current `main`, this PR adds `meta/`
analysis, reproducible bounded map/proposal checks, and a prose-watchlist
extension. It changes no derivation seed, theorem statement, or `prompt/`
file beyond the repairs already merged through PR #43.

## Findings

- Audits all 21 derivations with a row-level index of 782 ledger claims;
  F001–F013 and their repair custody are recorded in `meta/review/`.
- Classifies the named Lean state/step/path maps, restricted maps, object
  squares, renaming, swap, and a written ungraded adjunction; bounded checks
  and counterexamples are in `meta/immune_system/`.
- Compares the local construction with the pinned, read-only Genesis snapshot
  `dbccpage/19L57G1@89fc568a61eb22100edf4070d40eb1449c350ed4`.
  There is no imported authority, no Genesis source copied here, and no
  global categorical or evolutionary claim.
- Scores 28 candidates under a declared rubric, prototypes four before
  writing full seeds, and packages ten one-or-two-sentence proposals in
  `meta/next_ten/`. C11/C17 tie and are both retained.

## Validation receipts

The untouched-source baseline on the plan branch completed 51/51 native
commands with exit 0: 935 tests; coverage gate 99.78% line / 99.60% branch;
mypy; four existing CI gates; pinned offline Lean build; 21 evidence checks;
21 axiom-report writers. Full logs and exit codes are in
`meta/review/baseline/summary.json` and its numbered logs.

At exact source commit `6f60a16f378b57fadec3d087dfd3aebcec916ff1`,
the first meta-branch suite ran all 51 commands: 50 passed. The parallel
Lean build alone failed while reading existing Mathlib `.olean.private`
files. Those files existed and were hash-readable. All ten affected axiom
modules built sequentially, and the full pinned build then passed (3,160
jobs), without a package update or source change. A clean retry at the same
commit passed commands 1–39, including 935 tests, the 99.78% line and 99.60%
branch coverage gate, mypy, four CI gates, the full pinned Lean build, all
21 evidence `--check` commands, and the first ten axiom-report writers. The
user stopped the retry before the remaining 11 report writers and final
status command. All 21 report writers had passed in the first suite. Each
native check therefore has a passing exact-source receipt, while a single
uninterrupted 51/51 pass was not completed. The two command summaries are
`meta/review/meta_suite_first_summary.json` and
`meta/review/meta_suite_retry_summary.json`; detailed logs remain local.

The expanded prose watchlist passed with 22 watched digests and 213 hits
across 35 tracked files. The paper-pin comparison found 17 paper files with
pins before and after, with no count change. `prompt/` has no diff, no
`.lake` path is tracked, and the only untracked path is the preexisting
user-owned `AGENTS.md`.

## Integration after PR #43

PR #43 merged as `460c6e623636f69f588f6f123d4974b1c6a3086c`; its tree
equals the repair head tested by the 52-command suite. This branch then
integrated that `main`. The sole content conflict was `paper/change_log.md`:
both entries were retained as items 39 and 40. Against merged `main`,
`code/`, `evidence/`, `lean4/`, and `tests/` are identical; under `ci/`, only
the deliberate prose watchlist differs, and under `paper/`, only the change
log differs. The integrated tree passed the axiom-citation detector, exact
checks for all ten proposal packages, the unchanged-paper-pin comparison,
and the prose watchlist. No new full-suite pass is claimed for this merge.

## Limits

The correspondence audit labels derived, computed, refuted, chosen, and open
claims separately. Finite map checks use the declared two-term binary
universe; historical defect counts have different review units. The ten
seeds are proposals, not completed derivations. The user explicitly
requested publication after the local review.
