# Proposed plan and stopping conditions

**Status: chosen proposal outside the derivational seal.** Parent: `prompt/eighteenth/seed_prompt.md`. Only this package's seed and the parent are inputs for a future derivation. No result in this plan is a theorem of the proposed seed.

## Reading and alternatives

Chosen: a reading is an ordered choice of zero, one, or two terms and records the induced assertions; equality compares sets of records. Unchosen: compare multisets of readings; keep if it differs.

## Questions to derive or refute

Find the smallest pair of distinct written results with identical local records, or refute such a pair within the bound.

## Rule-5 re-check

The eighteenth state and steps stay fixed; only result equality changes. The quotient map is total on states but needs a congruence check on steps. Every inherited claim must be cited and checked on the new seed; a map of states alone is insufficient for a claim about paths.

## Phases

1. Write the notion/source-status table and list every unchosen reading, including the exact sentence declining it.
2. Implement typed bounded state, step, answer, sameness and exploration code. Attempt every change, fewest additions first, for at most 100 rounds. Export the exact frontier, an independent count, and comparison receipts against the parent.
3. Lean targets: Define local records and equivalence, prove reflexive/symmetric/transitive, then check whether a step descends to equivalence classes. Print axioms for every cited theorem. If a target cannot be closed within a bounded attempt, mark it open or prove it on paper with a separate check; do not silently weaken it.
4. Generate deterministic evidence twice and compare hashes. Write paper, ledger and change log with claim status, evidence and falsifier; put known-result names only in the final paper section.
5. Run all native gates, check `git diff --stat -- prompt/`, inspect `.lake` staging, and commit in small coherent checkpoints.

## Bounds and stopping

At most four terms with yes/no assertions, exhaustive orbit and local-record counts; initial short rounds. Raise the bound only if it completes in minutes on this machine. Stop after 100 rounds or earlier if no new bounded result appears. At most two full paper/ledger review passes after the first draft. Stop and report if a step requires network, a file outside the repository, a change to `prompt/`, or a question. Completion requires all tests, coverage, mypy, Lean, axiom citations, prose and evidence checks green, no unsupported claim, and a clean intended tree.
