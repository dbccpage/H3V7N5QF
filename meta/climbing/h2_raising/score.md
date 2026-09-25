# H2 score against the frozen prediction

**Status:** operator's scoring, 2026-09-25, outside the seal. Nothing in the
prediction is edited.

**Integrity checks, done before scoring:**

- `git show 24cdfd9:meta/climbing/h2_raising/prediction.md | sha256sum`
  gives `f44817cd494ae36828c323a86acbe76b3621c81d124b9d0b83001e8e7082b3e6`,
  which equals `prediction.sha256`.
- The file was last changed in `9209ef7`. That commit is an ancestor of the
  install (`57260a5`, #49) and of the run's first commit as replayed
  (`5ff679c`; run id `e712a1f`). The run started from a history-free
  snapshot clone (`8404d1b`) that held no `meta/`.

**Evidence scored:** `paper/twentythird/paper.md`, `claim_ledger.md`,
`evidence/twentythird/summary.json`, `given.json` and `results_*.csv`, and
the axiom report `lean_axioms.txt`, at `24cdfd9` (PR #50). Every Lean name
cited below is in that report.

**Grades** (as for H1):

- HIT: the run established the item as predicted.
- PARTIAL: some parts hit, and at least one part missed or was not
  addressed.
- MISS: the run refuted the item or found otherwise.

## Table

| item | prediction, in brief | score | evidence |
|---|---|---|---|
| Q0 | In the twenty-second nothing asserted is never the same as something asserted, since its sameness keeps every difference. Here `xry`, `ysx` on two terms is `x` raised, so it is the same as nothing. | **HIT** | D3: `same22_nothing_iff`, `raisedPair_nothing` (`a b; arb bsa` is nothing here) and `raisedPair_not_nothing22` (not there), the prediction's own witness. The paper is sharper on the twenty-second's side. A *state* asserting a pair equally often in both relations is already nothing there (`state_asserting_something_is_nothing22`, `a; ara asa`). A result whose plain state asserts something is not, which is the prediction's claim read on results. |
| Q1 | Two results are the same exactly when they have equally many terms and every closed sequence has the same sum. Raising changes no loop's sum and no return's sum. | **HIT** | D1: `gen3_iff_same3`, `genW3_iff_sameW3` (excesses differing by `g(x) − g(y)`); `excess_raise` touches no loop; `Same3.loop`, `Same3.twoWay`, `Same3.around` keep the sums. The prediction's closed-sequence form is the same criterion by D2's argument applied to the difference of two excess tables; D14 uses it as the complete description on three terms. Computed `generated_sameness`: 234 states, 5 and 33 classes, matching the mark. |
| Q2 | A result is exact exactly when every closed sequence sums to zero; sequences of one, two and three terms suffice. | **HIT** | D2: `same3_nothing_iff`, `sameW3_nothing_iff`. "No longer sum is ever needed." |
| Q3 | Every survivor carries a closed sequence of one, two or three terms with a non-zero sum. It is computed from the result alone, holds on every member and fails on every exact result. Survivors: `xrx`; `xry` alone; `xry`, `ysx` on three terms, where `x, y, z` sums to 1. | **HIT** | D2: `Same3.loop`, `Same3.twoWay`, `Same3.around`; `nothing_certificate`; `nothing_mismatch` empty in every run. Three-term witness `arcThree_not_nothing` (`a b c; arb bsa`, sum around one). The one- and two-term survivors carry their certificates in `results_bound2_rounds24.csv` (`a b; brb`: "loop 1 = 1"; `a b; bra`: "two-way 0 1 = 1"). |
| Q4 | Adding a term does not respect the sameness (`xry`, `ysx`, then add `z`: sum 1 against 0). Growth creates survivors; the result reached depends on the member. Two readings kept: (S) change states, form results afterwards, round = first round a member is reached; (X) a change of a result is a change of any member. | **HIT** | D4: `addTerm_not_respected`, `step_of_same3_fails`, the prediction's witness. C-E is (S) word for word, with the same round. C-X is (X). *Note:* the paper holds the two as compatible choices, C-X for what a change of a result is and C-E for the exploration and its rounds, rather than as rival readings. What parts them is scored under Q6. |
| Q5 | Identifying two terms breaks the sameness once three terms remain (witness: `x` raised on `x, u, v, y`, then `u` with `v`). With at most two remaining it respects it. Adding an assertion respects it; a removal has an addition's result. | **HIT** | D4: identifying respects the sameness with at most three terms and not with four. The witness has the prediction's shape: `a b c d` against `c` raised, then `a` with `b`, giving a sum around of one (`given.json`). `respect_mismatch` empty over 38,379 outcomes. Additions and removals: D4 (22:D2 imported). The evidence is a computed witness and a written proof, not Lean (O2), within the prediction's "Lean or computed witness". |
| Q6 | Under (S) the cost is terms plus the fewest assertions of a member. Under (X) it is terms plus the loops' and returns' sums without sign. `xry`, `ysx` on three terms costs 5 under (S) and 3 under (X). Under (X) round 3 is infinite. | **PARTIAL** | *Hit:* the (S) formula (D5: `cost3_iff`, `cost3_iff_min`). `a b c; arb bsa` costs 5 (D6, `adding_a_term_raises_the_cost` at `k = 1`; `results_bound3_rounds10.csv`, written `a b c; crb bsc`: round 5, cost 5). The fact beneath the (X) claim is proved: from `a b` (cost 2), adding a term to the member raised `k` times reaches a result of cost `3 + 2k`, for every `k` (`adding_a_term_raises_the_cost`, N4). *Not addressed:* no cost or round is defined under (X). The (X) formula, the cost 3, and "round 3 is infinite" appear nowhere; the paper's rounds are (S)'s only. |
| Q7 | Members with the fewest exist. Their count is at least the loops' plus returns' part, with equality on at most two terms. On three terms `xry`, `ysx` has fewest 2 against 0. Not unique: that result has three, one on each pair. Exact exactly when the fewest is 0. | **PARTIAL** | *Hit:* existence and the criterion (D5, D7: `fewest_iff`); the lower bound and its equality with at most two terms (D5(a), `cost3_two`); fewest 2 against a bound of 0 on `a b c; arb bsa` (cost 5 against the bound 3 in `results_bound3_rounds10.csv`); non-uniqueness (N7: `a b; arb arb` and `a b; arb bra`, `readBack3_none`); exact exactly at the fewest 0 (D2 with D5: the result asserting nothing costs `n`). *Miss:* the witness count. At a fixed writing the result has three such members, one on each pair. But turning the terms round carries each into the next, and the run counts states up to writing, so it has exactly one: `states_asserting_the_fewest` is 1 for `a b c; crb bsc` in `results_bound3_rounds10.csv` and `results_bound5_rounds8.csv`, and the map back answers it. |
| Q8 | Exchanging `r` and `s` negates every difference and turns raising into its reverse. It is a symmetry of results, fewest changes and exactness. | **HIT** | D13: `same3_swap_iff`, `cost3_swap`, `reach3_swap`; "negates every excess and turns `g` into `−g`". Exactness goes with the sameness (the negated sums of the result asserting nothing stay zero). `exchange_mismatch` empty. |
| Q9 | No earlier seed of the line (seventh, ninth, twenty-second) maps one to one. Witness: `xry` twice against `xry`, `yrx`, one result here, two in each of those seeds. Every result here is some twenty-second result's; exactly those differing by raising merge. The rung repairs within its level; the pair of maps of the twenty-second's kind is not available. | **HIT** | D9: `seventh_pair_apart`, `twentysecond_pair_apart`, `ninth_pair_apart`, `seventh_pair_merge`, on the prediction's own witness `a b; arb arb`, `a b; arb bra`; `carried_additions_merge3` (any map carrying additions to the same additions merges them). K2: every result has a state asserting the fewest that is a twenty-second result. D11, `merge_loses3`: the merges are those by raising. *Residue:* whether a map carrying each change to *some* change is one to one is left open (O4). The prediction's "of the twenty-second's kind" is the refuted class. |

**Tally:** 8 HIT, 2 PARTIAL, 0 MISS.

Both partials come from the prediction's own framing. Q6 asked for costs under a reading, (X), that the run named but never measured. Q7 counted members at a fixed writing, where the run counts up to writing.

## What the run found that the prediction did not say

- **The twenty-second's question, split.** A state can be the same as
  nothing while asserting something; a result cannot (D3).
- **Cost structure.**
  - There are closed forms on two and three terms.
  - The loops and returns do not fix the cost: two results with the same
    ones cost 6 and 12 (`loops_and_two_way_do_not_fix_the_cost`).
  - The minimum is reached by raising sets of terms while the count falls,
    and single terms do not suffice from four terms on
    (`four_single_terms_do_not_find_the_fewest`).
- **Parity and step size.** Every change moves the cost by an odd number
  (`Step.cost3_odd`). A change from a state asserting the fewest moves it by
  at most one (`Step.cost3_le`) (D6).
- **The map back exists.** The prediction expected no pair of maps. The run
  gave the one-to-one half's refutation and a map back to the twenty-second's
  results. The smallest results it answers "none" on cost four: six of them,
  all on two terms (`readBack3_some_of_cost_le_three`, D10).
- **The first seed's pair.** `a b c; arb arc` and `a b c; bra cra` are one
  result here (`first_pair_merge`).
- **Counts.** Two-term results recording `t` assertions number
  `2t² + t + 1`, and rounds grow as `2r²` (D14).
- **Readings.** Raising every term at once gives back the twenty-second's
  results (C-H2, `raise_all_gen`). Raising each term at most once gives
  C-H1's sameness (C-H3). Both "asserted together" readings survive with
  raising (D16).
- **Other results.** Reachability holds (D12). Two additions of different
  pairs undo each other on two terms (D15). Twenty-one of the earlier
  statements now depend on which state of a result is read (D17).

## Caveats

- **Blindness.** The run started from snapshot `8404d1b`: one commit, no
  parent, no `meta/`. The operator audited the transcripts from outside and
  found no outside vocabulary and no `meta/` path (PR #50). The run did not
  see this prediction.
- **Operator acts** (PR #50), none carrying content:
  - The first launch stopped before writing anything: the fresh clone was
    an untrusted workspace.
  - The operator resumed the session once with the bare word "continue",
    passing the settings' own allow and deny lists unchanged.
  - The operator landed the run's commits by cherry-pick; `range-diff`
    showed all five as `=`.
- **Rubric.** The author accepted the two recorded points at merge.
  - L3: "orient" is shorter, but would strike the parent's clause.
  - L5: the rung pair was expected to fail. As run, the one-to-one half
    fails with a witness (Q9), and the map-back half holds with a "none"
    witness at cost four.
- **Grading.** Every result is "blind (operator-targeted)" (ruling D1).
- **Not filled here.** `record.md` (rubric, "The rung record") is not written
  for H2, as it was not for H1.
