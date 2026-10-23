# Operator review tools

AuthorityEffect: None.

This area is outside the derivational inputs. Its old receipts and scores
describe their recorded source heads, not the latest repository state.

## Current replay recipe

`run_full_suite.py` extends the historical baseline commands with every current
evidence and axiom-report launcher under `code/`, both Lean package builds,
and the existing citation check. Each build reads its package's `lean-toolchain`.
There are currently 25 evidence checks and 25 report writers. No new check,
threshold, hosted workflow, or merge requirement is introduced.

From the repository root, with the existing Python test/type tools and both
Lean packages' offline dependencies already available:

```text
python meta/review/run_full_suite.py --out meta/review/local-replay-unique
```

Use a fresh output directory for each replay. Exit 0 means every listed child
command exited 0; inspect `summary.json` and each command's log. Exit 1 means
at least one child failed. Report writers can refresh tracked evidence: inspect
the final Git status. This runner does not isolate child tools from the network;
do not launch it when Lean would need to fetch dependencies.

## Historical recipe and focused regression

`run_baseline.py`, `baseline/`, and the retained suite summaries remain unchanged.
That historical recipe has 21 evidence/report families and one Lean build. It
is not the current all-25 replay recipe.

The small regression tests inspect command plans without executing the suite:

```text
python -m unittest discover -s meta/review -p test_run_full_suite.py -v
```

A passing plan test is not a passing full-suite receipt or a Lean build.
