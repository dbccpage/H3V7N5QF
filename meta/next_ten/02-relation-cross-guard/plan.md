# Proposed plan and stopping conditions

**Status: chosen proposal outside the derivational seal.** Parent: `prompt/ninth/seed_prompt.md`. Only this package's seed and the parent are inputs for a future derivation. No result in this plan is a theorem of the proposed seed.

## Reading and alternatives

Chosen: the guard is checked on the current ordered pair before the addition. Unchosen: check the whole relation after addition; keep it if it changes results.

## Questions to derive or refute

One term with both loops is not reached in three changes, while the ninth reaches it. Test whether identification can make both relations assert one pair later.

## Rule-5 re-check

The guarded state is the ninth state. Each guarded step embeds into a ninth step; the reverse map is partial at cross-relation additions. Every inherited claim must be cited and checked on the new seed; a map of states alone is insufficient for a claim about paths.

## Phases

1. Write the notion/source-status table and list every unchosen reading, including the exact sentence declining it.
2. Implement typed bounded state, step, answer, sameness and exploration code. Attempt every change, fewest additions first, for at most 100 rounds. Export the exact frontier, an independent count, and comparison receipts against the parent.
3. Lean targets: Define guarded steps, embed them into ninth steps, prove the local guard, give a blocked pair witness, and test an identification bypass. Print axioms for every cited theorem. If a target cannot be closed within a bounded attempt, mark it open or prove it on paper with a separate check; do not silently weaken it.
4. Generate deterministic evidence twice and compare hashes. Write paper, ledger and change log with claim status, evidence and falsifier; put known-result names only in the final paper section.
5. Run all native gates, check `git diff --stat -- prompt/`, inspect `.lake` staging, and commit in small coherent checkpoints.

## Bounds and stopping

At most three terms and three counted assertions, initially six rounds; independent finite census and exact frontier. Raise the bound only if it completes in minutes on this machine. Stop after 100 rounds or earlier if no new bounded result appears. At most two full paper/ledger review passes after the first draft. Stop and report if a step requires network, a file outside the repository, a change to `prompt/`, or a question. Completion requires all tests, coverage, mypy, Lean, axiom citations, prose and evidence checks green, no unsupported claim, and a clean intended tree.
