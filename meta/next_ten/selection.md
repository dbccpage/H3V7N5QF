# Candidate selection (outside the derivational seal)

**Status: chosen measure.** The hypothesis in each row is open; the score is a selection device, not a theorem. Weights were fixed in `rubric.md` before any proposal seed was written. `candidates.json`, `rank.py`, and `prototype_results.json` make the choice reproducible.

## Selected ten

| Rank | Candidate and package | Parent | Score | Hypothesis tested |
|---:|---|---|---:|---|
| 1 | C19 [`01-remove-bare-term`](01-remove-bare-term/why.md) | seventh | 92 | A bare-term removal destroys the empty state's one-way reachability. |
| 2 | C21 [`02-relation-cross-guard`](02-relation-cross-guard/why.md) | ninth | 89 | A local cross-relation guard breaks independent addition and may still be bypassed by identification. |
| 3 | C09 [`03-given-first-change`](03-given-first-change/why.md) | ninth | 87 | A given change shifts reachability and cost without a given assertion. |
| 4 | C07 [`04-written-refusal`](04-written-refusal/why.md) | twentyfirst | 85 | Written sameness and refusal interact beyond a quotient of the same closure. |
| 5 | C01 [`05-refusal-memory`](05-refusal-memory/why.md) | seventeenth | 84 | A refusal record can change later reachability. |
| 6 | C04 [`06-written-budget`](06-written-budget/why.md) | ninth | 81 | A state-carried budget changes reachability beyond the study's round bound. |
| 7 | C05 [`07-two-term-readings`](07-two-term-readings/why.md) | eighteenth | 80 | Sameness by local readings differs from both written equality and FREE rewriting. |
| 8 | C25 [`08-record-order`](08-record-order/why.md) | sixteenth | 79 | Order-sensitive feedback changes the result quotient and admission paths. |
| 9 | C11 [`09-two-step-leftover`](09-two-step-leftover/why.md) | tenth | 78 | Two-step clearing has outcomes beyond the one-step bare-term criterion. |
| 10 | C17 [`10-swap-as-change`](10-swap-as-change/why.md) | ninth | 78 | Making the existing involution a step changes shortest paths and sequence counts. |

C11 and C17 tie at 78; both are kept. C06 is scored in the full list but excluded after its prototype exposed an unresolved obstruction-answer rule. C08 is retained as a scored candidate but demoted by its bounded result-set comparison. These decisions precede the ten complete seeds.

## All scored candidates

| Candidate | Parent | Score | Disposition |
|---|---|---:|---|
| C19 remove-bare-term | seventh | 92 | selected |
| C06 partial-with-loops | nineteenth | 89 | excluded by prototype |
| C21 relation-cross-guard | ninth | 89 | selected |
| C09 given-first-change | ninth | 87 | selected |
| C07 written-refusal | twentyfirst | 85 | selected |
| C01 refusal-memory | seventeenth | 84 | selected |
| C04 written-budget | ninth | 81 | selected |
| C05 two-term-readings | eighteenth | 80 | selected |
| C25 record-order | sixteenth | 79 | selected |
| C11 two-step-leftover | tenth | 78 | selected |
| C17 swap-as-change | ninth | 78 | selected |
| C02 copy-alternative | ninth | 77 | not selected |
| C03 shared-terms | ninth | 77 | not selected |
| C14 admission-gates-change | fifteenth | 77 | not selected |
| C12 coarser-term-writing | thirteenth | 76 | not selected |
| C08 leftover-loop-refusal | sixteenth | 75 | not selected |
| C18 count-cap-two | fourth | 74 | not selected |
| C22 explicit-outcome-obstruction | seventeenth | 73 | not selected |
| C24 finite-letters | third | 73 | not selected |
| C28 refusal-count | twentyfirst | 73 | not selected |
| C10 reverse-changes | third | 72 | not selected |
| C26 refusal-copy | twentyfirst | 71 | not selected |
| C15 change-as-term | ninth | 70 | not selected |
| C20 split-term | sixth | 70 | not selected |
| C27 one-relation-start | ninth | 69 | not selected |
| C16 unfilled-boundary | ninth | 67 | not selected |
| C23 alternate-order | twentieth | 65 | not selected |
| C13 persistent-leftover | fourteenth | 56 | not selected |

## Independent ±50 percent sensitivity

Each row changes just one weight. A tie at the tenth-place score keeps **all** tied candidates in that row; `retained` can therefore exceed ten. This does not change the declared baseline selection.

| Axis | Factor | Enter | Leave | Tied cutoff | Retained |
|---|---:|---|---|---|---:|
| H | 0.5 | C18 | C25 | no | 10 |
| H | 1.5 | C02, C03, C14 | C11, C17 | yes | 11 |
| N | 0.5 | — | — | no | 10 |
| N | 1.5 | C02, C03 | C11, C17 | no | 10 |
| R | 0.5 | C02, C03 | C11, C17 | no | 10 |
| R | 1.5 | — | — | no | 10 |
| C | 0.5 | C08 | C25 | no | 10 |
| C | 1.5 | C02, C03 | C04 | yes | 11 |
| M | 0.5 | C02, C03 | C11, C17 | no | 10 |
| M | 1.5 | — | — | no | 10 |
| G | 0.5 | — | — | no | 10 |
| G | 1.5 | C02, C03, C14 | C11, C17 | yes | 11 |
| L | 0.5 | C02, C03 | C11, C17 | no | 10 |
| L | 1.5 | — | — | no | 10 |

**What does not follow:** the baseline top ten is not invariant under the declared weight perturbations. The H half-weight run replaces C25 with C18, while the N half-weight run keeps the baseline ten; these are two legal weightings with different and same selections. The computed table reports every axis and both directions.
