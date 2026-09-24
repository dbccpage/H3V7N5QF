# Repair cited axiom receipts and evidence custody

## Scope

Repair branch `review/whole-repo-2026-09-23` has local commit
`e5d02ddab4373a7c35eb0eaafad7b9972234d01d` atop the plan-only commit
`8f2c5179159b7dbdb9db06d39c47cb084abddb0f`. The starting local main
was `53b319a48f347b1a52e823ea7db46c79f8434c42`. No theorem
statement, seed, or `prompt/` file changed.

## Repairs

- Ten derivations cited Lean declarations absent from their own axiom
  reports (F001–F010). The appropriate `#print axioms` requests, report
  bytes, and manifests are committed together.
- Eighth and fifteenth receipt fields now call their models instead of
  writing fixed values (F011–F012). Injection tests mutate the source
  computation and observe the receipt change.
- Eight inherited closed-item ledger cells now cite the source or generated
  series already named in their rows (F013). Their statuses and claim scope
  remain the same.
- `ci/check_axiom_citations.py` checks backticked local theorem/lemma
  citations against each derivation's own generated report. A test removes
  the real second-derivation `Reach.legal` report line, observes rejection,
  restores it, and observes a pass. The gate does not prove English claims
  or resolve ambiguous short citations on its own.

## Validation receipts

The untouched-source baseline on the plan branch completed 51/51 native
commands with exit 0: 935 tests; coverage gate 99.78% line / 99.60% branch;
mypy; four existing CI gates; pinned offline Lean build; all 21 evidence
`--check` runs and 21 axiom-report writers. Logs and exact exit codes are
in `meta/review/baseline/summary.json` (on the independent meta branch).

The full repair-branch suite, including the added citation detector, passed
**52/52 commands** at exact head `e5d02ddab4373a7c35eb0eaafad7b9972234d01d`
from 2026-09-23 17:43:36 to 18:54:58 America/New_York. It recorded 940
passing tests; 99.78% line and 99.60% branch coverage under the gate; mypy;
five CI gates; pinned `lake build` (3,160 jobs); 21 evidence `--check` runs;
and 21 axiom-report writers. Every command has exit code 0 in
`meta/review/repair_suite/summary.json` and its numbered logs (on the
independent meta branch). `git diff --exit-code HEAD -- code/ paper/
evidence/ ci/ lean4/ prompt/` was empty, `git diff --stat -- prompt/` was
empty, and no `.lake` path is tracked. The only status entries were the
preexisting untracked `AGENTS.md` and the uncommitted `meta/` package.

## Limits

The repair restores claim/evidence custody; it does not extend any finite
bound or assert a new theorem. The user explicitly requested publication of
this PR after the local review.
