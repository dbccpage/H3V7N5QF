# Derivation reading index

Generated from the current local files. These counts and snippets are navigation
aids, not evidence of a theorem or of a completed audit.
The single-ID count excludes grouped ledger rows such as base `G1–G14`;
`claim_audit.csv` counts those rows separately.

## base

- Parent: none.
- Source sizes (bytes): seed 1216; paper 33481; ledger 14357; change log 27745; evidence.py 17927.
- Single-ID ledger rows: 49; printed axiom names: 47.
- Disagreement fields: (none).
- Summary top keys: attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. Alternatives: kept, or eliminated by proof / 8. Open / 9. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | The seed read with multiplicity of assertions | open | not explored | — | a model of states with multiplicity and its exploration |
  - | O2 | Number of new results in rounds 21–100 | open | determined by D8; not computed | — | a count up to sameness for up to 102 terms |
  - | O3 | Lean proof that changes commute with rewriting of terms (carries `fewest_changes_A/B` to every writing; used by D8, D9, D10) | open in Lean; proved on paper; computed within the bound | paper §4 (D8) | — | a Lean proof |
  - | O4 | Results beyond the declared bound, listed | open | frontier exported | — | a larger run |
  - | O5 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | — |
  - | O6 | Lean proof of D5 for a sequence of changes (the Lean statements are for one change) | open in Lean; argued on paper (D5) | paper §4 (D5) | — | a Lean proof |

## second

- Parent: base.
- Source sizes (bytes): seed 1193; paper 41621; ledger 20954; change log 8555; evidence.py 20687.
- Single-ID ledger rows: 60; printed axiom names: 72.
- Disagreement fields: (none).
- Summary top keys: anchored_census, attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. Alternatives: kept, or eliminated by proof / 8. Open / 9. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | The seed read with multiplicity of assertions | open | not explored | — | 1:O1 | a model with multiplicity and its exploration |
  - | O2 | Number of new results in rounds 21–100 | open | determined by D8, D9; not computed | — | 1:O2 | a count up to sameness for up to 102 terms |
  - | O3 | Lean proof of the "if" direction of D12 when the carrying map merges terms | open in Lean; proved on paper; computed within 3 terms | paper §4 (D12) | — | — | a Lean proof (the identifications along the map) |
  - | O4 | Results beyond the declared bounds, listed | open | frontier exported (bounds 5 / 4); census counts at 5 | — | 1:O4 | a larger run |
  - | O5 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | 1:O5 | — |
- Seed diff:

```diff
--- base
+++ second
@@ -12 +12 @@
-A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
+A change is exactly one of: identifying two terms; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
```

## third

- Parent: second.
- Source sizes (bytes): seed 1102; paper 48611; ledger 27840; change log 8282; evidence.py 21284.
- Single-ID ledger rows: 64; printed axiom names: 125.
- Disagreement fields: checked, round_not_raised_by_one, counts_lowered_by, fewest_classes_lowered_by.
- Summary top keys: anchored_census, attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. Alternatives: kept, or eliminated by proof / 8. Open / 9. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | The seed read with multiplicity of assertions | open | not explored | — | 1:O1, 2:O1 | a model with multiplicity and its exploration |
  - | O2 | Number of new results in rounds 21–100 | open | determined by D8, D9; not computed | — | 2:O2 (the same set) | a count up to sameness for up to 102 terms |
  - | O3 | Results beyond the declared bounds, listed | open | frontier exported (bounds 5 / 4); census counts at 5 | — | 2:O4 | a larger run |
  - | O4 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | 2:O5 | — |
  - | O5 | A closed form for the number of sequences reaching a result | open | computed per result within the bound (K7); no formula sought | — | — | a formula agreeing with every computed count |
- Seed diff:

```diff
--- second
+++ third
@@ -12 +12 @@
-A change is exactly one of: identifying two terms; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
+A change is exactly one of: adding a term; adding an assertion. Nothing else is a change.
```

## fourth

- Parent: third.
- Source sizes (bytes): seed 1228; paper 62068; ledger 33074; change log 10587; evidence.py 32239.
- Single-ID ledger rows: 66; printed axiom names: 158.
- Disagreement fields: checked, round_not_raised_by_one, counts_lowered_by, fewest_classes_lowered_by.
- Summary top keys: anchored_census, attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. Alternatives: kept, or eliminated by proof / 8. Open / 9. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | The seed read with multiplicity of assertions | closed: given by the fourth seed | `prompt/fourth/seed_prompt.md`; this derivation | — | 1:O1, 2:O1, 3:O1 closed | — |
  - | O2 | Number of new results in rounds beyond the bound | given by the series for any round (D14, `layer_counts`); computed to round 20 in every `rounds_*.csv`, to round 100 with two terms (D17); not listed | — | — | 3:O2 | a listing |
  - | O3 | Results beyond the declared bounds, listed | open | frontier exported (both parts); census counts at 5 terms | — | 3:O3 | a larger run |
  - | O4 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | 3:O4 | — |
  - | O5 | A closed form for the number of sequences reaching a result with three or more terms | open | computed per result within the bound (K7); two terms closed (D17) | — | 3:O5 narrowed | a formula agreeing with every computed count |
  - | O6 | A closed form, written out, for the number of results with `n ≥ 3` terms at round `r` | open | the series of D14 computes it for every `n`, `r` (`counts_upto`, `layer_counts`) | — | — | a formula per `n` agreeing with the series |
- Seed diff:

```diff
--- third
+++ fourth
@@ -3 +3 @@
-Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms.
+Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one.
@@ -7 +7 @@
-- `arb` is asserted.
+- `arb` is asserted with multiplicity one.
```

## fifth

- Parent: fourth.
- Source sizes (bytes): seed 1382; paper 65612; ledger 30439; change log 11031; evidence.py 38264.
- Single-ID ledger rows: 69; printed axiom names: 165.
- Disagreement fields: checked, cost_raised_by_more_than_one, cost_rule_disagreements, names_told_apart_again, lowering, round_raised, round_kept, round_lowered.
- Summary top keys: anchored_census, attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. What survives removal and identification / 8. Alternatives: kept, or eliminated by proof / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | The seed read with multiplicity | closed by the fourth seed | — | — | 4:O1 | — |
  - | O2 | Number of new results in rounds beyond the bound | given by the series and the cost formula (D14, `layer_counts`); not listed | — | — | 4:O2 | a listing |
  - | O3 | Results beyond the declared bounds, listed | open | frontier exported (both parts); census counts at 5 terms | — | 4:O3 | a larger run |
  - | O4 | Other readings of "build structure" | open as to records; closed as to results (D10) | paper §3 (C7) | — | 4:O4 | — |
  - | O5 | A closed form for the number of shortest sequences with three or more terms, or with the names one term | open | computed per result within the bound (K7); two terms, no destroyed given: `C(i + j, i)` (D17) | — | 4:O5 | a formula agreeing with every computed count |
  - | O6 | A Lean statement on counted states that identifying a build's added term back gives the would-be outcome | open (attempted once, not closed: change log 11) | computed (`is_build_of`); on supports Lean `Seed.build_gives_back` | std | 4:D10's reading | the Lean proof |
  - | O7 | Lean statements of D8(iv) (exactly which changes raise the cost by one) and of the exactness of the shortest-sequence counts (D14) | open: proved in the paper, checked by computation | paper §4; `summary.json` (`cost_rule_disagreements` empty) | — | — | the Lean proofs |
- Seed diff:

```diff
--- fourth
+++ fifth
@@ -3 +3 @@
-Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one.
+Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.
@@ -12 +12 @@
-A change is exactly one of: adding a term; adding an assertion. Nothing else is a change.
+A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
```

## sixth

- Parent: fifth.
- Source sizes (bytes): seed 1062; paper 62309; ledger 28905; change log 11483; evidence.py 40638.
- Single-ID ledger rows: 66; printed axiom names: 175.
- Disagreement fields: checked, cost_raised_by_more_than_one, cost_rule_disagreements, names_told_apart_again, lowering, round_raised, round_kept, round_lowered, xrx_made.
- Summary top keys: anchored_census, attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. What survives once nothing is forbidden / 8. Alternatives: kept, or eliminated by proof / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | The seed read with multiplicity | closed by the fourth seed | — | — | 4:O1 | — |
  - | O2 | Number of new results in rounds beyond the bound | given by the series and the cost formula (D14, `layer_counts`); not listed | — | — | 5:O2 | a listing |
  - | O3 | Results beyond the declared bounds, listed | open | frontier exported (both parts); census counts at 5 terms; two-term rounds in closed form (D17) | — | 5:O3 | a larger run |
  - | O4 | Other readings of "build structure" | without object | — | — | 5:O4 | — |
  - | O5 | A closed form for the number of shortest sequences with three or more terms, or with the names one term | open | computed per result within the bound (K7); two terms, names apart: a multinomial (D17) | — | 5:O5 | a formula agreeing with every computed count |
  - | O6 | The cost under the unchosen reading of identification with `bra` given | open: shown to differ from the chosen reading's (D19); not computed | paper §4 D19 | — | 5:D19 does not survive | a formula, or a computation under that reading |
  - | O7 | Lean statements of D8(iv), of the exactness of the shortest-sequence counts (D14), and of D19 | open: proved in the paper, checked by computation | paper §4; `summary.json` | — | 5:O7 | the Lean proofs |
- Seed diff:

```diff
--- fifth
+++ sixth
@@ -8 +7,0 @@
-- For no term `x` may `xrx` be asserted.
@@ -13,2 +11,0 @@
-
-A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing.
```

## seventh

- Parent: sixth.
- Source sizes (bytes): seed 1046; paper 51205; ledger 23699; change log 9042; evidence.py 33922.
- Single-ID ledger rows: 53; printed axiom names: 118.
- Disagreement fields: checked, cost_raised_by_more_than_one, size_not_moved_by_one, cost_rule_disagreements, term_lost, lowering, round_raised, round_kept, round_lowered, xrx_made.
- Summary top keys: attempts_in_full_log, census, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. What survives with nothing given / 8. Alternatives: kept, or eliminated by proof / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | A closed form for the number of shortest sequences reaching a result with two or more terms | open: computed per result within the bound (K7), exact there (D10); one for one-term results (D11) | `results_*.csv` | — | 6:O5 restated from the empty beginning | a formula agreeing with every compu
  - | O2 | Results beyond the declared bounds, listed | open: the frontier exported (both parts); the census counts at 6 terms; the two-term rounds in closed form (D11) | `frontier_*.csv`, `summary.json` | — | 6:O3 | a larger run |
  - | O3 | Lean statements of D10's completeness, D11's closed form, D12 and D15 | open: proved in the paper, checked by computation | paper §4; `summary.json` | — | 6:O7 | the Lean proofs |
  - | O4 | The earlier papers' O1 (multiplicity) and O2 (results beyond the bound, counted) | closed by the fourth seed; given by the series for any round (D10) | — | — | 6:O1, 6:O2 | — |
- Seed diff:

```diff
--- sixth
+++ seventh
@@ -5,5 +5 @@
-Given:
-
-- `arb` is asserted with multiplicity one.
-
-Whether `bra` is asserted is not given.
+Nothing is given: to begin with there are no terms and nothing is asserted.
```

## eighth

- Parent: seventh.
- Source sizes (bytes): seed 1140; paper 54457; ledger 26005; change log 10317; evidence.py 35165.
- Single-ID ledger rows: 55; printed axiom names: 140.
- Disagreement fields: checked, cost_raised_by_more_than_one, cost_rule_disagreements, names_told_apart_again, lowering, round_raised, round_kept, round_lowered, xrx_made, xsx_made.
- Summary top keys: anchored_census, attempts_in_full_logs, free_cost_closed_form_checked_on, free_cost_closed_form_mismatches, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. What survives the second relation / 8. Alternatives: kept, or eliminated by proof / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | A closed form for the number of shortest sequences with three or more terms, or with the names one term | open: computed per result within the bound (K7); two terms, names apart: the multinomial of D11 | `results_*.csv` | — | 6:O5 with four more items | a formula agreeing with every computed
  - | O2 | Results beyond the declared bounds, listed | open: frontier exported (both parts); census counts at 4 terms; two-term rounds in closed form (D11) | `frontier_*.csv`, `summary.json` | — | 6:O3 | a larger run |
  - | O3 | Lean statements of D3, of D4(iv), of the exactness of the shortest-sequence counts (D10), of D11, of D15 and of the non-product count (D10) | open: proved in the paper, checked by computation | paper §4; `summary.json` | — | 6:O7 | the Lean proofs |
  - | O4 | The cost from a beginning asserting something with `s` | open: the formula of C2″, proved in the paper; not computed | paper §3 | — | — (new) | a computation from such a beginning |
  - | O5 | The earlier papers' O1 (multiplicity) and O2 (results beyond the bound, counted) | closed by the fourth seed; given by the series for any round (D10) | — | — | 6:O1, 6:O2 | — |
- Seed diff:

```diff
--- seventh
+++ eighth
@@ -3 +3 @@
-Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.
+Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.
@@ -5 +5,5 @@
-Nothing is given: to begin with there are no terms and nothing is asserted.
+Given:
+
+- `arb` is asserted with multiplicity one.
+
+Whether `bra`, or anything written with `s`, is asserted is not given.
```

## ninth

- Parent: eighth.
- Source sizes (bytes): seed 1093; paper 61828; ledger 30262; change log 7453; evidence.py 45514.
- Single-ID ledger rows: 61; printed axiom names: 151.
- Disagreement fields: checked, cost_raised_by_more_than_one, size_not_moved_by_one, cost_rule_disagreements, term_lost, lowering, round_raised, round_kept, round_lowered, xrx_made, xsx_made.
- Summary top keys: attempts_in_full_log, census, given, independent_counts, plan, reachability, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. What survives with nothing given and two relations / 8. Alternatives: kept, or eliminated by proof / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | A closed form for the number of shortest sequences reaching a result with two or more terms | open: computed per result within the bound (K7), exact there (D10); with one term it is `C(p + q, p)` (D11) | `results_*.csv` | — | 7:O1, 8:O1 restated from the empty beginning with two relations | a
  - | O2 | Results beyond the declared bounds, listed | open: the frontier exported (both parts); the census counts at 6 terms; the two-term rounds in closed form (D11) | `frontier_*.csv`, `summary.json` | — | 7:O2, 8:O2 | a larger run |
  - | O3 | Lean statements of D3's change-count formula, D10's completeness, D11's closed form and binomial, D12, D15 and the non-product count (D10) | open: proved in the paper, checked by computation | paper §4; `summary.json`; `Step9.proj` is not a statement of D3's formula | — | 7:O3, 8:O3 | the Lea
  - | O4 | The eighth paper's O4 (cost from a beginning asserting something with `s`) | open: moot for the chosen beginning; not computed | paper §3 | — | 8:O4 remains | a computation from such a beginning |
  - | O5 | The earlier papers' O1 (multiplicity) and O2 (results beyond the bound, counted) | closed by the fourth seed; given by the series for any round (D10) | — | — | 7:O4, 8:O5 | — |
- Seed diff:

```diff
--- eighth
+++ ninth
@@ -5,5 +5 @@
-Given:
-
-- `arb` is asserted with multiplicity one.
-
-Whether `bra`, or anything written with `s`, is asserted is not given.
+Nothing is given: to begin with there are no terms and nothing is asserted.
```

## tenth

- Parent: ninth.
- Source sizes (bytes): seed 1343; paper 14469; ledger 7896; change log 4329; evidence.py 15689.
- Single-ID ledger rows: 17; printed axiom names: 26.
- Disagreement fields: (none).
- Summary top keys: given, plan, reading, runs, tagged.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What leftover is / 5. What of the ninth survives / 6. The unchosen tag / 7. The task's questions / 8. What does not follow / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Lean of D8 | open in Lean | paper §4 D8; Python `bare_criterion` against `restores_in_one` | — | — | a Lean proof of the bare-term criterion |
  - | O2 | `leftoverOf s.swap t.swap = leftoverOf s t` for identifications | open in Lean | `leftover_swap_addTerm`, `_remove`; 9:D16 `Step9.swap` | — | — | a counterexample under swap |
  - | O3 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11 | — | 9:O2 | — |
- Seed diff:

```diff
--- ninth
+++ tenth
@@ -8,0 +9,2 @@
+After every change, record what that change leaves. A leftover is not an assertion. Nothing left, a leftover that a later change of the four kinds can clear, and a leftover that none of them can, are three outcomes. Declare which, for every change.
+
```

## eleventh

- Parent: ninth.
- Source sizes (bytes): seed 1325; paper 14390; ledger 7568; change log 4126; evidence.py 17003.
- Single-ID ledger rows: 17; printed axiom names: 24.
- Disagreement fields: (none).
- Summary top keys: given, labeled, plan, reading, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What a writing is / 5. What of the ninth survives / 6. The unchosen label / 7. The task's questions / 8. What does not follow / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11 | — | 9:O2 | — |
  - | O2 | Reading a determining colliding writing is not the identification of the collided terms | open in Lean | paper §9; Python `read_from` vs `perform` identify | — | — | a Lean identity of those two operations |
- Seed diff:

```diff
--- ninth
+++ eleventh
@@ -8,0 +9,2 @@
+A writing of terms may give two terms the same letter while they remain two terms. Assertions are read from the writing. If two terms are written the same and their assertions differ, the writing does not determine the assertions.
+
```

## twelfth

- Parent: ninth.
- Source sizes (bytes): seed 1237; paper 13918; ledger 6671; change log 3418; evidence.py 15439.
- Single-ID ledger rows: 15; printed axiom names: 20.
- Disagreement fields: (none).
- Summary top keys: given, plan, reading, recorded, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What the record is / 5. What of the ninth survives / 6. The unchosen recorded tag / 7. The task's questions / 8. What does not follow / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11 | — | 9:O2 | — |
  - | O2 | Lean record of other-term groups vs the 2×2 block | open in Lean | paper §9; Python `record_rel` outgoing/incoming | — | — | a Lean identity of those two records |
- Seed diff:

```diff
--- ninth
+++ twelfth
@@ -7 +7 @@
-A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
+A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. Identifying two terms records, for each relation, which assertions of those two terms become one assertion. The record is kept with the result.
```

## thirteenth

- Parent: ninth.
- Source sizes (bytes): seed 1334; paper 14486; ledger 7042; change log 3610; evidence.py 16012.
- Single-ID ledger rows: 15; printed axiom names: 22.
- Disagreement fields: (none).
- Summary top keys: coarse, given, plan, reading, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What the coarser writing is / 5. What of the ninth survives / 6. The unchosen coarser result / 7. The task's questions / 8. What does not follow / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Results beyond the declared bounds | open as a listing | ninth frontier; 9:D11; seventh two-term form for C-C2 | — | 9:O2 | — |
  - | O2 | Number of finer preimages up to rewriting of terms | open in Lean | paper §9; Python `splits` in a fixed writing | — | — | a Lean enumeration of preimages up to rewriting |
- Seed diff:

```diff
--- ninth
+++ thirteenth
@@ -8,0 +9,2 @@
+A coarser writing of an assertion forgets whether it was written with `r` or with `s`. For every result, record also its coarser writing. Two results that differ only in which relation wrote their assertions may be the same coarser result.
+
```

## fourteenth

- Parent: ninth.
- Source sizes (bytes): seed 1246; paper 13837; ledger 7683; change log 4416; evidence.py 17270.
- Single-ID ledger rows: 16; printed axiom names: 30.
- Disagreement fields: (none).
- Summary top keys: given, plan, reading, runs, tagged.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What leftover is / 5. What of the ninth survives / 6. The unchosen tag / 7. The task's questions / 8. What does not follow / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Results beyond the declared bounds | open | ninth frontier; 9:D11 two-term closed form | — | 9:O bounds | a complete run of 100 rounds within minutes |
  - | O2 | A Lean function `Step9 s t → LeftWriting` | open in Lean | paper §9; Python `leftover_of`; Lean `leftoverRemove` takes the pair, not a `Step9` | — | — | a definition eliminating `Step9` into `LeftWriting` without `Prop`→`Type` |
- Seed diff:

```diff
--- ninth
+++ fourteenth
@@ -8,0 +9,2 @@
+After every change, record what that change leaves. A leftover is written neither `xry` nor `xsy`. A leftover is not an assertion and is not an answer.
+
```

## fifteenth

- Parent: ninth.
- Source sizes (bytes): seed 1276; paper 13950; ledger 7857; change log 4314; evidence.py 16537.
- Single-ID ledger rows: 16; printed axiom names: 26.
- Disagreement fields: (none).
- Summary top keys: given, plan, reading, runs, tagged.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What admission is / 5. What of the ninth survives / 6. The unchosen tag / 7. The task's questions / 8. What does not follow / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Results beyond the declared bounds | open | ninth frontier; 9:D11 two-term closed form | — | 9:O bounds | a complete run of 100 rounds within minutes |
  - | O2 | A Lean function `Step9 s t → Admission` | open in Lean | paper §9; Python `admission_of_reaching`; Lean `reaching` is of the result, not a `Step9` | — | — | a definition eliminating `Step9` into `Admission` without `Prop`→`Type` |
- Seed diff:

```diff
--- ninth
+++ fifteenth
@@ -8,0 +9,2 @@
+A result of the changes is reached. Whether it is admitted is not given by the reaching. Record for every result whether it is admitted. Reaching a result does not make it admitted.
+
```

## sixteenth

- Parent: fourteenth.
- Source sizes (bytes): seed 1333; paper 34272; ledger 20116; change log 7084; evidence.py 37935.
- Single-ID ledger rows: 45; printed axiom names: 76.
- Disagreement fields: (none).
- Summary top keys: alternatives, attempts_in_full_log, given, independent_counts, plan, reachability, reading, runs.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. The same relation, and the other / 5. The cost / 6. The mass, and reachability / 7. Termination, and the record's growth / 8. The results and the count / 9. What of the earlier derivations survives / 10. The unchosen readings (D14) / 11. The task's questions / 12. What does not follow / 13. Open / 14. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | Results beyond the declared bounds | open: the frontier exported; the series gives every round | `frontier_*.csv`, `counts.csv` | — | 9:O2 | a larger run |
  - | O2 | A reachability criterion for the set reading C-R2 | open: neither the ninth's nor the carrying criterion agrees with search | `alternatives.json` | — | — | a criterion agreeing with search |
  - | O3 | The sufficiency half of the carrying criterion in Lean | open: computed on 27 889 pairs; necessity in Lean through the mass | `summary.json` (`reachability`); Lean `Reach16.mass_le` | — | — | the Lean proof |
  - | O4 | The diagonal mass in Lean | open: computed (`diagonal_mass_fell` empty) | `summary.json` | — | — | the Lean proof |
  - | O5 | A closed form for the shortest-sequence counts with two or more terms | open: exact counts within the bounds | `results_*.csv` | — | 9:O1 | a formula |
  - | O6 | Changes commute with rewriting (`rename16`) in Lean | not attempted in Lean; the sameness is implemented and every check is up to it | `code/sixteenth/state.py` `canonical16` | — | 9:D7 not carried over | the Lean proof |
- Seed diff:

```diff
--- fourteenth
+++ sixteenth
@@ -9 +9 @@
-After every change, record what that change leaves. A leftover is written neither `xry` nor `xsy`. A leftover is not an assertion and is not an answer.
+After every change, record what that change leaves. A leftover is written neither `xry` nor `xsy`. A recorded leftover `xℓy` may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion.
```

## seventeenth

- Parent: base.
- Source sizes (bytes): seed 1175; paper 25188; ledger 12453; change log 6954; evidence.py 11966.
- Single-ID ledger rows: 34; printed axiom names: 47.
- Disagreement fields: replace_has_xrx, replace_not_base, replace_cost_mismatch, replace_not_formula, perform_misses_witness, perform_cost_not_above, m_disagree_loopfree, m_agree_on_loop, remove_first_differs, refusal_changes_something, loop_beginning_in_replace, loop_beginning_not_in_perform, replace_results, perform_results, frontier, by_run, unexpanded_by_run.
- Summary top keys: bound, by_run, frontier, loop_beginning_in_replace, loop_beginning_not_in_perform, m_agree_on_loop, m_disagree_loopfree, passes, perform_cost_not_above, perform_misses_witness, perform_results_summed_over_runs, refusal_changes_something, remove_first_differs, replace_cost_mismatch, replace_has_xrx, replace_not_base, replace_not_formula, replace_results_summed_over_runs, rounds, runs, unexpanded_by_run.
- Paper headings: 0. Findings in brief / 1. What the seed gives / 2. Notions and their sources / 3. Readings that had to be chosen / 4. What follows / 5. What does not follow / 6. The exploration / 7. Which base results survive / 8. Alternatives kept / 9. Open / 10. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O2 | A closed form for the fewest A-perform changes | open | D6 refutes the base formula; no replacement | — | — | a proved formula, checked against the rounds |
  - | O3 | A path that leaves the term bound cannot be shorter than the recorded A-perform round | open | paper §6 | — | — | a proof, or a witness path |
  - | O4 | The A-perform closure equals the well-formed states inside the bound | open | no listing; K2 is the frontier instead | — | the base orbit count counts loop-free states only | a count that matches the closure |
  - | O5 | The base cost at a writing other than `a = 0`, `b ∈ {0, 1}` | open | D9 carries the steps; D5 does not claim the other writings | — | 1: the same open rewriting of the cost | a Lean theorem without that hypothesis |
- Seed diff:

```diff
--- base
+++ seventeenth
@@ -8 +7,0 @@
-- For no term `x` may `xrx` be asserted.
```

## eighteenth

- Parent: base.
- Source sizes (bytes): seed 1218; paper 8847; ledger 5032; change log 1614; evidence.py 5982.
- Single-ID ledger rows: 14; printed axiom names: 6.
- Disagreement fields: writings_called_the_same, orbit_formula_fails, rounds_below_the_base_cost.
- Summary top keys: bound, rounds, given_orbit, given_aut, given_equals_its_swap, base_calls_them_the_same, runs, anchored_closures_equal_for_both_bra, free_closures_equal_for_both_bra.
- Paper headings: 0. Findings in brief / 1. Readings / 2. What is the same result / 3. What the changes reach / 4. The reading that was not run / 5. What survives / 6. Open / 7. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | A closed form for 137 and 69 | open | K1, K2 | — | — | a formula checked against the runs |
  - | O2 | Without the names: a return from four terms cannot be shorter than the recorded round. (With the names: closed by D3.) | open | section 6 | — | — | a proof, or a shorter witness |
- Seed diff:

```diff
--- base
+++ eighteenth
@@ -16 +16 @@
-Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are the same result.
+Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are different results.
```

## nineteenth

- Parent: base.
- Source sizes (bytes): seed 1221; paper 6639; ledger 3340; change log 1164; evidence.py 5232.
- Single-ID ledger rows: 14; printed axiom names: 11.
- Disagreement fields: sets_differ, extra_beyond_base, term_dropped, cooccur_performed, obstruction_not_between, removal_answer_outside.
- Summary top keys: bound, rounds, anchored_closures_equal_for_both_bra, free_closures_equal_for_both_bra, runs.
- Paper headings: 1. Notions / 2. What one chosen assertion does / 3. What is reached / 4. What does not follow / 5. What survives of the base / 6. Open / 7. Nearest known results, and how the findings differ
- Open ledger rows:
  - | O1 | A closed form for 68 and 19 | open | the rounds in N9 | — | a proved formula | — |
- Seed diff:

```diff
--- base
+++ nineteenth
@@ -12 +12 @@
-A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
+A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in one chosen assertion.
```

## twentieth

- Parent: base.
- Source sizes (bytes): seed 1220; paper 7432; ledger 2983; change log 1426; evidence.py 5840.
- Single-ID ledger rows: 11; printed axiom names: 8.
- Disagreement fields: layer_mismatch, frontier_mismatch, additions_track_rounds, differs_from_base, o2_closure_differs.
- Summary top keys: bound, rounds, runs, capped_by_round_2.
- Paper headings: 1. Notions / 2. The two listings / 3. Additions are not the round / 4. The other reading / 5. What does not follow / 6. What survives of the base / 7. Open / 8. Nearest known results, and how the findings differ
- Open ledger rows:
  - (none)
- Seed diff:

```diff
--- base
+++ twentieth
@@ -16 +16 @@
-Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are the same result.
+Attempt every change, fewest total changes first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are the same result.
```

## twentyfirst

- Parent: base.
- Source sizes (bytes): seed 1076; paper 6087; ledger 2527; change log 1405; evidence.py 4427.
- Single-ID ledger rows: 9; printed axiom names: 9.
- Disagreement fields: outside_the_base, answer_buys_a_result, stopped_at_the_start.
- Summary top keys: bound, rounds, runs.
- Paper headings: 1. Notions / 2. What refusal does / 3. What is reached / 4. What does not follow / 5. What survives of the base / 6. Open / 7. Nearest known results, and how the findings differ
- Open ledger rows:
  - (none)
- Seed diff:

```diff
--- base
+++ twentyfirst
@@ -14 +14 @@
-A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing.
+A change that makes some `xrx` asserted is obstructed. An obstructed change is refused. A refused change is recorded and changes nothing.
```
