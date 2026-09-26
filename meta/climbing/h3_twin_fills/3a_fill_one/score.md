# H3 twin 3A ("fill one") score against the frozen prediction

**Status:** operator's scoring, 2026-09-25, outside the seal. Nothing in the
prediction is edited.

**Integrity checks, done before scoring:**

- `git show c2e8efe:meta/climbing/h3_twin_fills/3a_fill_one/prediction.md | sha256sum`
  gives `dbbc9d39707c4c74bdd4e8e53a8dd31daca795b9e66a5c2bed1c8bd077e3d1d9`,
  which equals `prediction.sha256`.
- The file was last changed in `03970e4`. That commit is an ancestor of the
  install (#52) and of the run's first commit as replayed (`7c668ba`; run id
  `14d049e`). The run started from snapshot `c8e10f7`, which held no
  `meta/`.

**Evidence scored:** `paper/twentyfourth/paper.md`, `claim_ledger.md`,
`evidence/twentyfourth/summary.json`, `given.json`, `results_*.csv` and
`lean_axioms.txt`, at `c2e8efe` (PR #53). Every Lean name cited below is in
that report. Grades are as for H1 and H2.

## Table

| item | prediction, in brief | score | evidence |
|---|---|---|---|
| A0 | The twenty-third's record names no term: `a b; ara` and `a b; arb` record the same and are kept by a loop and by a return. | **HIT** | D3: `record23_does_not_show_which`, on the prediction's own pair, and a three-term pair (`record23_does_not_show_which_three`). 17 of 37 records are shared by results kept by different numbers of terms (`given.json`). |
| A1 | A filled term balances exactly when its loop's difference is zero, the same on every member and in every writing. | **HIT** | D2: `balances_iff`, `Same24.balances`, `SameW24.balances`; `balance_mismatch` empty. |
| A2 | Filled terms are part of the state. `a` and `a` filled are two results, and the twenty-third's results are exactly those with nothing filled. | **HIT** | C-S (the sameness names no filling); D13: `same24_ofSt_iff`, `twentythird_mismatch` empty; D14: `smallest_none` (`a` filled is its own result). |
| A3 | Told apart implies survivor. Converse fails: `a b; arb` and `a b c; arb bsa` with every term filled. A survivor can be told apart by some filling exactly when a loop is non-zero. | **HIT** | D4 and D5: `told_iff`, `told_not_nothing`, `told_after_fill`, `never_told_of_loops_zero`. The prediction's witnesses are the paper's: `twoWayFilled_never_told`, `aroundFilled_never_told`. |
| A4 | A merged term's loop is the loops plus the returns of the merged terms, the same on every member. `a b; arb`, identified, then filled, is told. A sum around three terms never reaches a loop: `a b c; arb bsa` merged, then filled, always balances. | **PARTIAL** | *Hit:* D6. For two terms, the merged loop is the two loops plus the return between them. `identify_tells` is the prediction's witness. Identifying any two terms of `a b c; arb bsa` gives the result asserting nothing on two terms. *Not addressed:* that the merged loop is the same on every member, where identifying does not respect the sameness; and the general statement for any set of merged terms. The paper states the two-term formula and the one witness only. |
| A5 | Cost is terms plus filled terms plus fewest assertions (fillings counted under another reading). Round equals cost. The cheapest told-apart result is `a; ara` filled, at three changes; none takes two or fewer. | **HIT** | D8: `cost24_eq`, `round_not_cost` empty. C-F2 counts fillings and gives other results, each round its counted cost (`readings.json`). In every run the cheapest told result costs 3: `a; ara` and `a; asa`, filled (`results_*.csv`; first told in `given.json`). |
| A6 | Identifying a filled term with an unfilled one gives filled or unfilled by reading; both are kept. Whether refilling is a change is open in the seed. | **HIT** | C-I1 is chosen. C-I2 and C-I3 are kept and computed; they give other outcomes for 41 and 46 of 113 identifications. C-F1 chooses refilling as no change; C-F1′ and C-F2 are the alternatives (§3). *Note:* the readings of identifying give the same results and rounds. They part on outcomes, on reachability and on parity (D9, D11), which the prediction did not say. |
| A7 | The exchange keeps balance and is a symmetry of results, cost and record. | **HIT** | D12: `same24_swap_iff`, `balances_swap`, `told_swap`, `cost24_swap`, `reach24_swap`; `exchange_mismatch` empty. |
| A8 | The twenty-third maps one to one as "nothing filled", with changes carried. Forgetting returns every mapped result. The inverse on the image answers "none" exactly with a filling; smallest `a` filled, two changes. No merge. | **HIT** | D13: `same24_ofSt_iff`, `Step.toStep24`, `no_merge`. D14: `readBack_ofSt`, `readBack_none_iff`, `smallest_none`, `smallest_none_unique`. The forgetting map answers every result and returns mapped ones (`Step24.forget`; `forget_merges` shows what it loses). |
| A9 | Fill one tells apart every one-term survivor at three changes, reads loops only, and never tells `a b; arb` or `a b c; arb bsa`. | **HIT** | D4 and D5 (`told_iff`, `never_told_of_loops_zero`); A5's cost 3. |

**Tally:** 9 HIT, 1 PARTIAL, 0 MISS.

## What the run found that the prediction did not say

- **The parent's record shows *whether*.** A result records no assertion
  exactly when it is the one asserting nothing (`record_whether`).
- **Parity breaks.** Identifying two filled terms moves the cost by an even
  number: `a b` both filled costs 4, and identified costs 2
  (`identify_two_filled_even`). It is the only change that does.
- **Reachability breaks under the chosen reading.** A filled term never goes
  away (`Reach24.hasFilled`), so the twenty-third's criterion fails exactly
  from a result with a filling to one without
  (`twentythird_criterion_fails`). Under C-I2 and C-I3 it holds.
- **Survivors not told fall into three kinds.** They are one filling away,
  or kept by two terms, or kept by three (`not_told_cases`).
- **Other findings.** Shortest sequences to a one-term result are no longer
  unique (D10). The two-term counts have closed forms per number of filled
  terms (D15).

## Caveats

- **Operator acts** (PR #53):
  - The author paused and resumed the work.
  - The run was resumed twice with a bare "continue". The second time was
    because its process exited while its own check was still running,
    despite the task's foreground-gates sentence.
  - The landing joined shared registration hunks, keeping both sides.
  - No second-model review took place before the merge.
- **Blindness.** Both transcripts are outside the repository and carry no
  outside vocabulary and no `meta/` path (PR #53).
- **Grading.** "Blind (operator-targeted)" (ruling D1).

## The order test and the twins together (ruling D2)

The packet (§5) predicted that the two orders disagree. Each part is scored
against both papers:

| part | score | evidence |
|---|---|---|
| Fill one tells apart the cheapest survivors (`a; ara`, three changes) and reads loops only | **HIT** | 3A D4 and D5; the cheapest told result is 3 in every run |
| Fill three tells apart, under the direct reading, the survivors whose loops and returns cancel (`a b c; arb bsa`), and reads no loop | **HIT** | 3B `arcThree_told`, `cone_decides`, `around_add_loop`, `loop_unseen` |
| Each tells apart survivors the other never does | **HIT** | Only fill one: `a; ara`, `a b c; ara`. Only fill three: `a b c; arb bsa` (3A `aroundFilled_never_told`) |
| Neither tells apart `a b; arb` or `a b c; arb bra bsc csb` | **HIT** | 3A `never_told_of_loops_zero`. 3B `nothing_filled_of_lt_three`; the second is blind by `blind_three_iff` |
| Fill one first: a told result at 3 changes against 5 | **HIT** | Round 3 in 3A's runs. Round 5 in 3B's runs with three terms or more, first `a b c; crb` filled `a c b` (`results_*.csv`) |

**Joint note.** The two orders do not agree, and neither contains the
other.

- **What each reads.** The licence order's member, fill one, reads loops,
  and reads them first and most cheaply. The outside order's member, fill
  three, never reads a loop. It reads sums around three terms, and a return
  one way round (3B `arb_one_way`).
- **What neither reads.** On two terms, neither tells apart a survivor kept
  by a return. The returns are the residual both twins leave, and "fill
  two" in the frozen class is the member that reads them.
- **How far fill three reaches.** 3B found that fill three's reach grows
  with the terms. With five terms or more, every triple filled tells apart
  every survivor whose loops are zero (`blind_five`). Blind survivors exist
  only on three and four terms. So the two fills together, with every term
  and every triple filled, tell apart every survivor on five terms or more.
  On two terms they tell apart only the loop survivors.
- **What the comparison shows.** The licence rule orders the loop reading
  first, as the packet expected. The comparison answers D2's question
  within this frozen class only.
