# H3 twin 3B ("fill three") score against the frozen prediction

**Status:** operator's scoring, 2026-09-25, outside the seal. Nothing in the
prediction is edited.

**Integrity checks, done before scoring:**

- `git show c2e8efe:meta/climbing/h3_twin_fills/3b_fill_three/prediction.md | sha256sum`
  gives `7aff4f0ea1cd3b680db13496c79284420948a7890e586c2a10611e0aae8acc4f`,
  which equals `prediction.sha256`.
- The file was last changed in `03970e4`. That commit is an ancestor of the
  install (#52) and of the run's first commit as replayed (`8632860`; run
  id `ab4df3f`). The run started from snapshot `c8e10f7`, which held no
  `meta/`.

**Evidence scored:** `paper/twentyfifth/paper.md`, `claim_ledger.md`,
`evidence/twentyfifth/summary.json`, `given.json`, `readings.json`,
`results_*.csv` and `lean_axioms.txt`, at `c2e8efe` (PR #53). Every Lean
name cited below is in that report. Grades are as for H1 and H2.

**Readings.** The prediction's "direct reading" is the run's C-B1 (chosen),
and its "both-ways reading" is C-B2 (kept).

## Table

| item | prediction, in brief | score | evidence |
|---|---|---|---|
| B0 | The twenty-third's record names no term: `a b; ara` and `a b; arb` record the same and are kept by a loop and by a return. | **HIT** | D3: `record_pair_two_terms`, on the prediction's own pair, and a three-term triple of witnesses (`record_does_not_show_which_terms`). |
| B1 | Direct: balance iff the sum around is zero. Both-ways: iff the three returns sum to zero. Raising changes neither, so balance is recorded per result. | **HIT** | D1: `around_norm`, `Same25.balanced_iff`; `record_mismatch` empty. C-B2 in §3: the two-way sums add to zero, "which no raising moves either". |
| B2 | The seed leaves open whether reverse assertions count and whether the way round is fixed. The readings give different records (witness `a b c; arb brc cra`). At least two are kept. | **HIT** | §3: C-O1 (chosen) against C-O2, C-O3 and C-O4, and C-B1 against C-B2, all kept and computed with different figures (`readings.json`: 30, 25, 7, 104 and 42 told). *Note:* the paper's witness is `arb_one_way` (`a b c; arb`: 1 one way round, 0 the other), not the prediction's. The prediction's witness gives 3 against 0 under the paper's C-B1 definition. |
| B3 | Told implies survivor. Direct reading, loops and returns zero: exact iff not told with every triple filled both ways. Both-ways reading: `a b c; arb bsa` balances. Never told under either reading: every survivor on one or two terms; `a b c; ara`; `a b c; arb bra bsc csb`. | **HIT** | D4: `told_iff`, `told_not_nothing`, `nothing_balanced`. D7: `cone_decides`. §3: under C-B2, `a b c; arb bsa` balances either way round. D5: `nothing_filled_of_lt_three`, `loop_unseen`. D6: `blind_three_iff` (returns adding to zero and the sum around zero) covers the prediction's cancelling-returns witness. The paper's own is `a b c; arb arc csb csa` (`blind_three_not_nothing`). |
| B4 | Identifying inside a filled triple: no kept reading leaves a filling on fewer than three different terms. | **MISS** | The run kept and computed C-I3, which keeps the triples left without three different terms. Under it, `a b` with the triple `a a b` is reached at round 5, and the cost of D8 and reachability both fail (§3, D16; ledger C-I3, N9). The first sentence of B4 only restates the seed's "three different terms". |
| B5 | Cost is terms plus fillings plus fewest assertions, and round equals cost. A told result needs at least five changes; five suffice (`a b c; arb`, filled the way it reads). | **HIT** | D8: `cost25_eq`, proved both ways; `round_not_cost` empty. In the five- and three-term runs the first told results are at round 5: `a b c; crb` and `a b c; csb`, filled `a c b` (`results_*.csv`). |
| B6 | The exchange negates every sum, keeps balance under both readings, and is a symmetry of results, cost and record. | **HIT** | D14: `around_swap`, `balanced_swap`, `told_swap`, `same25_swap_iff`, `cost25_swap`, `reach25_swap`; `exchange_mismatch` empty. The both-ways case is not stated. It follows from the negation of every difference. |
| B7 | The twenty-third maps one to one as "nothing filled", with changes carried. Forgetting returns mapped results. "None" exactly with a filling; smallest three terms filled, nothing asserted, four changes. No merge. | **HIT** | D10: `embed_same_iff`, `embed_step`. D11: `readBack25_embed`, `readBack25_none_cost`, `readBack25_none_smallest`, `cost_oneFilled`. D12: `forget_same`, `forget_loses`. |
| B8 | Fill three tells no survivor on one or two terms and never reads a loop. Its cheapest told result costs five. Under the direct reading, with every triple filled, it tells every survivor whose loops and returns are zero, such as `a b c; arb bsa`, which fill one never does. | **HIT** | `nothing_filled_of_lt_three`, `around_add_loop`; B5's round 5; `cone_decides`, `arcThree_told`. The contrast is from 3A (`aroundFilled_never_told`). |

**Tally:** 8 HIT, 0 PARTIAL, 1 MISS.

## What the run found that the prediction did not say

- **The parent's record shows *whether*** (`record_shows_whether`).
- **When filled triples decide.** When the loops and returns are zero, a
  set of filled triples decides exactly when its sums around have rank
  `C(n − 1, 2)` (D7).
  - The triples through one term always decide.
  - On four terms, any three of the four triples decide.
  - On five terms the fewest that decide are six, and 125 of the 210
    labelled sets of six do.
- **How far blindness reaches.** A survivor with every triple balancing
  both ways exists on three and four terms (`blind_three_iff`,
  `blind_four_not_nothing`). With five terms or more, only the loops escape
  (`blind_five`).
- **Parity breaks.** Identifying two terms of a filled triple drops it and
  moves the cost by an even number, 4 to 2 (`parity_fails`).
- **Reachability holds** under the chosen reading (`reach25_criterion`) and
  fails under C-I3.
- **A two-way sum is seen one way round only** (`arb_one_way`).

## Caveats

- **Operator acts** (PR #53):
  - The author paused and resumed the work.
  - The run was resumed once with a bare "continue".
  - The landing joined shared registration hunks, keeping both sides. One of
    them, `ci/check_definitional_citations.py`, was not on the packet's
    list.
  - No second-model review took place before the merge.
- **Blindness.** The transcripts carry no outside vocabulary and no `meta/`
  path. The paper's final section names outside results, as the task
  allows.
- **Grading.** "Blind (operator-targeted)" (ruling D1). 3B's member was
  installed as "not the smallest; chosen by the operator" (rubric L3).

## The order test and the twins together (ruling D2)

The order test is scored in full in `../3a_fill_one/score.md`: **5 of 5
parts HIT**. The two orders disagree.

- Fill one tells apart a survivor first, at 3 changes against fill three's
  5, and reads loops only.
- Fill three reads sums around three terms, and returns one way round, and
  never reads a loop.
- Each tells apart survivors the other never does. On two terms, neither
  tells apart a survivor kept by a return. Those returns are what "fill two"
  in the frozen class reads.
- Fill three's reach grows with the terms. From five terms on, every triple
  filled tells apart every survivor whose loops are zero (`blind_five`). The
  two fills together then tell apart every survivor.
- The verdict holds within the frozen class only.
