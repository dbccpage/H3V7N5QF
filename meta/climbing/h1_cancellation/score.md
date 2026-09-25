# H1 score against the frozen prediction

**Status:** operator's scoring, 2026-09-26, outside the seal. Nothing in the
prediction is edited.

**Integrity checks, done before scoring:**

- `git show 90f4479:meta/climbing/h1_cancellation/prediction.md | sha256sum`
  gives `97dd4116eb49f6a9a595c5fc2a81d8d298fb36a36e8065f2f438cf6758999ed4`,
  which equals `prediction.sha256`.
- The file was last changed in `8900c53` (PR #46). That is before the
  install (#47) and before the run's first commit (`6234077`).

**Evidence scored:** `paper/twentysecond/paper.md`, `claim_ledger.md`,
`evidence/twentysecond/summary.json` and `given.json` at `90f4479` (PR #48).

**Grades:**

- HIT: the run established the item as predicted.
- PARTIAL: some parts hit, and at least one part missed or was not
  addressed.
- MISS: the run refuted the item or found otherwise.

## Table

| item | prediction, in brief | score | evidence |
|---|---|---|---|
| P1 | Two results are the same exactly when, after rewriting, they have equally many terms and the same difference at every ordered pair. Each has exactly one plain form. | **HIT** | D1: `gen_iff_same`, `same_iff_excess`, `count_plain`, `plain_reduced`, `plain_rename`. Computed `generated_sameness`: 1,242 states, 247 classes, `sameness_mismatch` empty. |
| P2 | Identifying, adding a term and adding an assertion respect the sameness. Removal does not, so at least two readings of removal are kept. The record splits: on written assertions it depends on the member reached; on the plain form it is the spread. | **PARTIAL** | *Hit:* the three kinds respect it (`Same.identify`, D2); two readings of a result's changes are kept (C-X, C-X′); the record splits (C-R: the plain state, chosen; the state a sequence reached, kept in the attempt log), and on the plain state it sums to the cost (`recorded_sum`). *Miss:* "removal does not respect the sameness" holds only kind by kind. On the plain state no removal of that pair exists (D6). But a removal from any state has the result of an addition from any other (`same_remove_add_partner`, `step_of_same`), so the two readings give the same results one change away (D2). They part only under the unchosen identification reading (D14). |
| P3 | Fewest changes from the beginning equal the spread under every kept reading. No change raises it by more than one, and identification never raises it. Additions attain it. | **HIT** | D4: `fewest_changes`, `fewest_changes_every_writing`, `Step.phi_le`, `Reach.phi_le`, `shortest_additions`, `reach_plainSt`. Identification moves the cost by −(1 + 2c) (D6, `record_identify`). Computed `round_not_cost` empty. |
| P4 | In the ninth no addition is undone, since each raises the size by one. Here `xsy` right after `xry` returns to the same result. | **HIT** | D5: `ninth_additions_never_return`, `…_every_writing`, `addition_undoes_addition`, `addition_undoes_not_in_ninth`. Computed `undo_failed` empty. |
| P5 | The step law fails for the spread (witness: identifying `x` with `z` in `xry`, `zsy` lowers it 5 → 2). It survives for the signed total, which moves by exactly one per change. So any sequence between two results has length at least the gap in signed totals, and the same parity. | **PARTIAL** | *Hit:* the law fails for the spread. An identification moves the cost by −(1 + 2c) with any `c` (D6, `record_identify`, `identify_takes`, N6), and the witness is the case `c = 1`. The 5-term run has 1,242 identifications taking out two assertions. Parity also hits, in an equivalent form: the cost moves by an odd number (`Step.phi_parity`), and the spread and the signed total have the same parity. *Not addressed:* no statement or theorem says that the signed total (terms plus the sum of the differences) moves by exactly one. So the length bound by the gap in signed totals is not stated. D15's "`n + |D|` moves by at most one" is about the unchosen reading C-J2. |
| P6 | The exchange changes the sign of every difference, respects the sameness, and is an involution. It is a symmetry of results, fewest changes and reachability. | **HIT** | D10: `excess_swap`, `same_swap_iff`, `plain_swap`, `phi_swap`, `Step.swap`, `swap_swap`. Computed `exchange_mismatch` empty. |
| P7 | A result is reachable from another exactly when it has a term or the start is empty. The empty result is never returned to. | **HIT** | D9: `reach_criterion`, `reach_mutual`. D3: `empty_never_returned`. Computed `reach_mismatch` empty; K7. |
| P8 | Round `k` holds exactly the results of spread `k`. Their plain forms correspond one to one with the ninth's round-`k` results that carry no pair in both relations, under the same bound. | **HIT** | D4 with `round_not_cost` empty. D7: `plain_states_stay_apart_every_writing`, `state_of_result_and_together`. `ninth_derivation` in `summary.json`: each plain ninth result lands at its own round, one each, and they are exactly the results within the ninth's rounds (4,235 = 4,235 at 2 terms; `ninth_mismatch` empty in all three runs). |
| P9 | The ninth's states do not map one to one; the seventh's do. The map back answers "none" exactly where a difference is below zero, first on one term asserting `xsx` once. A merge loses the smaller of the two counts at each pair. | **HIT** | D8: `ninth_not_one_to_one`, `carried_additions_merge`, `Step7.embed`, `ofR_sameW_iff`, `readBack_ofR`, `same_ofR_of_readBack`, `readBack_asa`, `readBack_none_smallest`. The map back answers exactly the images, and N11 says a plain `s` assertion means "none". D7: `merge_loses`, `min(M_r, M_s)`. |

**Tally:** 7 HIT, 2 PARTIAL, 0 MISS.

## What the run found that the prediction did not say

- **Three readings of the changed sentence.**
  - C-J1: one pair, with `x = y` allowed. This is the chosen reading.
  - C-J2: the letters as placeholders. A result is `(n, D)`.
  - C-J3: `x ≠ y` only. Under C-X, round 3 is infinite.

  At 2 terms and 8 rounds they give 673, 29 and 1,081 results (D15,
  `readings.json`). The prediction assumed C-J1 without naming the others.
- **Which two additions undo each other.** At a fixed writing, two additions
  in a row return exactly when they are one pair in the two relations. With
  a rewriting, other pairs can return (D5, N5).
- **Counts.** A factor per cycle of pairs, and a closed form at two terms
  (D11). A one-term result has exactly one shortest sequence (D12).
- **A readings split.** Under the unchosen "larger of the two" reading of
  identification, C-X and C-X′ differ in the results one change away, though
  not in rounds (D14).
- **What a merge leaves.** A result's plain `r` and `s` parts are not free
  of each other (N7).

## Caveats

- **Blindness.** The run saw operator commit messages from #46 and #47,
  which summarize the rubric and the rulings, and file names under
  `meta/climbing/`. It did not see the prediction's content (PR #48). The
  rung pair that P9 scores was already required by the run's own task, so
  P9 is weak evidence of anything beyond following the task. P1 to P8 rest
  on the seed sentence alone.
- **Operator acts.** The session was resumed once with the bare word
  "continue", and the operator ran the pending checks once (PR #48). Neither
  act carried content.
- **Grading.** Every result is "blind (operator-targeted)" (ruling D1).
