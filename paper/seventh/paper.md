# What follows from nothing: counted assertions, four kinds of change, and an empty beginning

Seventh derivation. Input: `prompt/seventh/seed_prompt.md`. Task:
`prompt/seventh/prompt.md`. Claim IDs refer to `paper/seventh/claim_ledger.md`;
an ID written `1:D8` refers to the first derivation's ledger
(`paper/claim_ledger.md`, paper `paper/paper.md`), `4:D8` to the fourth's
(`paper/fourth/`), `5:D8` to the fifth's, `6:D8` to the sixth's
(`paper/sixth/`). Lean names in the namespace `Seed.Seventh` are in
`lean4/Seventh/`; names in `Seed.Sixth`, `Seed.Fifth`, `Seed.Fourth`, `Seed`
are the earlier derivations' (`lean4/Sixth/`, `lean4/Fifth/`, `lean4/Fourth/`,
`lean4/H3V7N5QF/`). Where a short name exists in two libraries the seventh's
is meant unless the namespace is written. The axiom report for every theorem
cited here, of any of the seven libraries, is `evidence/seventh/lean_axioms.txt`.
Computed files are in `evidence/seventh/`, written by
`python code/generate_seventh.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; the unchosen
readings are listed), **derived** (proved), **computed** (output of `code/`),
**refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the seventh seed, and the re-check says whether the result *survives
with nothing given and no names*. The re-check is one of five kinds. *(no
change)*: the statement mentions neither the given nor the names, so it stands
as it is. *(through the maps)*: a state of the sixth seed with its names
forgotten is a state of the seventh (`MSt.forget`), and every change of the
sixth is a change of the seventh on the forgotten states (`Step6.forget`,
`Reach6.forget`); a state of the seventh with a term, both names put on one of
its terms, is a state of the sixth (`NSt.name`), and every change of the
seventh on such a state is a change of the sixth on the named states, the
names following the merge (`Step7.name`, `Reach7.name`). So what the sixth
proved about one change or one sequence holds here for every change that
starts from a state with a term; the first change, from the empty state, no
naming reaches and is proved afresh. *(without object)*: the statement is
about the given, the names, `bra`, or the destroyed givens, none of which the
seventh seed has. *(re-proved)*: the earlier proof used the given or the names
and a statement covering the seventh's states is proved afresh. *(computed
again)*: a computed statement of the sixth derivation is re-run beside the
seventh exploration and compared on the results with a term. Results of the
earlier derivations that fail under the seventh seed are listed in §8.

## 0. Findings in brief

1. The seventh seed is the sixth (counted assertions, four kinds of change,
   nothing forbidden) with the given replaced by "nothing is given: to begin
   with there are no terms and nothing is asserted" (given, §1). There is no
   `a`, no `b`, no `bra` to be unsure of, and one beginning: the empty state.
   With no names the two readings of sameness of the earlier derivations
   coincide (D12), so there is one reading too.
2. **The first change can only add a term** (D1, `first_change_adds_term`), and
   **a term, once there, stays**: every change on a state with a term leaves a
   state with a term (D2). So the empty state is a result (round 0) that is
   never returned to — the seventh's one irreversible change, in place of the
   sixth's merge of the two names, which has no object.
3. **The results are every well-formed state, the empty one included** (D5).
   The sixth's results are exactly the results with at least one term: with
   their names forgotten, and once the seventh's results are named — computed
   again on every run (`same_results_as_sixth_derivation_any_rewriting`).
4. **The cost is the size.** Every change moves the size (terms plus the sum
   of the multiplicities) by exactly one, and additions alone reach every
   well-formed state from the empty one, so the fewest changes to a result is
   its size, every shortest sequence is additions only, and the round of a
   result is its size (D4). Nothing is destroyed because nothing is given to
   destroy: the sixth's cost, measured from `arb`, does not survive (the
   one-term state costs one change here and two there, D13); what survives is
   the size difference with `size(given) = 0`.
5. **Reachability: a term decides.** A result reaches another exactly when the
   other has a term or the first is empty (D8): mutual among the results with
   a term, one-way out of the empty state, any two results comparable, a
   two-change cycle at every result but the empty one (D9). The sixth's names
   criterion, through the naming map, says "always" on states with a term and
   survives there; the empty-state clause is new.
6. **Nothing about the asserting is forced from nothing.** Every well-formed
   state is a result, so of the eighteen statements tested none holds in every
   result — the sixth's "at least one term" fails at round 0 (D14, N1). What
   is forced is the first change, the cost of every result, the one-way exit
   from the empty state, and the number of changes of a result,
   `C(n, 2) + d + 1 + n²` (D3).
7. With at most two terms the results of round `r` are
   `[r = 0] + [r ≥ 1] + [r ≥ 2] · (C(r+1, 3) + [r even] · r/2) / 2` — cubic
   (D11), so the seed's 100 rounds with two terms would hold about two
   million results and 40 are run, the closed form being proved for every
   round. Within the bounds the exploration is complete, certified by the
   sixth's independent count with the empty state added (D10). Everything
   claimed as derived is in Lean, the every-writing statements included
   (target 5 of the plan closed on the single attempt); proved in the paper
   and checked by computation only: the within-bound completeness (D10), the
   two-term closed form (D11), and the coincidence of the two readings of
   sameness (D12).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2‴ | An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G11 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G12 | Two results that differ only in how their terms are written are the same result. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, prove what is complete within it. |
| G14 | Any outcome is valid. |

The sixth seed's G3′ ("`arb` is asserted with multiplicity one") and G5
("whether `bra` is asserted is not given") are replaced by G3″; nothing else
changes (`diff`; `research/seventh/reading_the_seed.md`). Every other sentence
is the sixth seed's word for word.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry`, multiplicity | given (G1, G2‴) | |
| adding raises a multiplicity by one; removing lowers it by one | given (G2‴) | |
| asserted = multiplicity at least one; the counted state | chosen (4:C1′, no change) | the fourth's model with its names left out (`names = None`) |
| a state with no terms | given (G3″) | the beginning; always representable in the model, now a result |
| `xrx` is an assertion | given (G2‴: `x`, `y` any terms) | nothing forbids it, as under the sixth |
| the names `a`, `b` | — (not in the seed) | without object; the naming map puts both on one term to cite the sixth |
| what is given: nothing | given (G3″) | the empty state; one beginning |
| `bra` | — (not in the seed) | without object |
| supply of letters not capped | chosen (C3) | harmless |
| `r` does not write a term | chosen (C9) | writing only |
| change, four kinds; what identifying does | given (G6, G7) | on the empty state one change: a term (D1) |
| the multiplicities of the pairs an identification merges add up | chosen (C5‴, no change) | unchosen: the larger of the two; same results, reachability and cost (D15) |
| removing what is not asserted, identifying a term with itself: not changes; adding what is asserted is a change | chosen (C5‴, no change) | |
| the order of the changes of a result | chosen (C6) | identifications and removals, a term, the assertions |
| destroyed given, the sixth's cost | — (not in the seed) | without object; the cost is the size (D4) |
| cost | derived (D4) | the size; no second term |
| result | chosen (C6) | a counted state up to sameness |
| the results, as a set | derived (D5) | every well-formed state, the empty one included |
| sameness | given (G12) | one reading: with no names the two readings coincide (D12) |
| terms and assertions added to what is given | given (G11) | the terms and the total multiplicity of the result; never negative |
| round; what counts as one change | chosen (C6) | the round of a result is its size (D4) |
| bound, frontier | given (G13) | bound on terms and on rounds: chosen (C8′) |
| shortest sequences reaching a result; sequences of every length | computed (K7); derived (D4, D9) | additions only, exact within the bound; infinitely many sequences to every result with a term, one to the empty state |
| reachability between results | derived (D8) | a term decides; mutual among the results with a term (D9) |
| parity of the cost | derived (D4) | every change moves it by one |
| counts of results by terms and total multiplicity | computed (K1) | the sixth's series, the empty state added |
| the one irreversible change | derived (D2) | leaving the empty state |
| separability (the task's word) | chosen reading (§7) | telling the two named terms apart, the sixth's one-way property; without object; replaced by having a term |
| what survives with nothing given | derived (§7; `Seventh/Compare.lean`) | see §8 for what does not |

## 3. Readings that had to be chosen

C3, C5‴, C6, C9 are the earlier derivations', unchanged; C8′ is the fourth's
to sixth's. The sixth's C2′ (what is given: `a`, `b`, `arb`, `bra` or not)
has nothing to read: the seed says what is given, and it is nothing. The
sixth's C4 (two readings of sameness) is no longer a choice: D12.

**C3. No cap on the number of terms.** The sequences used in the proofs of D4
and D5 never have more terms than the target; the sequence of D8 between two
results with a term, the sixth's, uses at most `max(terms) + 2`; as 6:C3.

**C5‴. What is a change.** As 6:C5‴: adding an assertion that is asserted
already is a change, and so is adding `xrx`; removing what is not asserted and
identifying a term with itself are not changes; the pairs an identification
merges have their multiplicities added up (`code/fifth/state.py`, imported;
Lean `NSt.identify`, the fifth's definition with the names left out).
Unchosen: the larger of the two. Under the seventh seed the two readings give
the same results, the same reachability and the same cost (D15), since no
shortest sequence and no sequence used in the proofs identifies terms with
anything asserted between them; the unchosen reading is kept as an
alternative that changes nothing computed here.

**C6. Results and rounds.** As 6:C6: a result is a counted state up to
sameness; round `k` performs every change on every result first reached in
round `k − 1`; every change counts one. Fewest additions first:
identifications and removals add nothing, then a term, then the assertions.
Round 0 is the empty state; round 1 is the one-term state asserting nothing,
the outcome of the one change the empty state has (D1). Unchosen: other
orders; the order cannot move a result to another round (D4: the round of a
result is its size).

**C8′. Bound on terms and on rounds.** As 4:C8′ to 6:C8′: within any bound
on terms the results are infinite, so every exploration is bounded in terms
and in rounds: 5 terms with 11 rounds; 3 terms with 14 rounds; 2 terms with
40 rounds; a counts-only census at 6 terms with 12 rounds. Full attempt log
at 2 terms and 4 rounds; reachability among the results of 3 terms and 6
rounds, along the changes among the results of 3 terms and 8 rounds (every
sequence the proof of D8 uses between two of them stays within their sizes).
One beginning and one reading, so a quarter of the sixth's runs; the bounds
were raised above the plan's targets after timing (`change_log.md`, item 9).
The seed's 100 rounds with two terms would hold about two million results
(D11) and are not run.

**C9.** `r` writes assertions, not terms.

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. The first change adds a term.** On the empty state the list of
changes has one entry, "add a term": there are no two terms to identify, no
assertion to remove, no terms between which to assert
(`first_change_adds_term`; `code/fifth/changes.py` `changes` on the empty
state, computed: `given.json`, `the_first_change_can_only_add_a_term`). The
outcome is the one-term state asserting nothing, the only result of round 1
(`the_first_round_is_the_one_term_state_alone` true in every run).

**D2. A term stays: the one irreversible change.** Every change on a state
with a term leaves a state with a term (`Step7.nonempty`: a term is added; an
assertion is between terms; a removal keeps the terms; an identification of
two terms keeps one), and so does every change on a well-formed state
(`Step7.nonempty_out`). Hence once a state has a term every later state has a
term (`Reach7.nonempty`), and the empty state is reached from a well-formed
state only from itself in zero changes (`reach7_empty_iff`,
`empty_never_returned`, `no_cycle_at_empty`). This replaces the sixth's D7
(the names once one term stay one term): through the naming map the names
of every state are one term, so 6:D7 holds vacuously along every sequence
from a state with a term (`names_merged_vacuous`) and says nothing.
Computed: in every run no change loses the last term (`term_lost` empty), and
exactly one result reaches what is given — itself
(`results_that_reach_what_is_given: 1`).

**D3. How many changes a result has.** A result with `n` terms and `d`
asserted pairs, diagonal pairs included, has `C(n, 2) + d + 1 + n²` changes,
`1 + n²` of them additions (6:D3, no change: the count mentions no name);
the empty state has one. Computed: `attempts_equal_formula` true in every
run. On a result asserting no `xrx`, `n` plus the number of related pairs of
its changes make some `xrx` asserted (6:D3's characterisation, through the
maps: it is a fact about a change and its outcome; computed:
`xrx_making_equal_sixth_formula` true in every run, with the sixth's own
function).

**D4. Fewest changes (cost).** For a well-formed state `G` let `size(G)` be
its number of terms plus the sum of its multiplicities. Then the fewest
changes from what is given to `G` is

    size(G)

— the first to sixth derivations' `size − size(given) + 2·lost` with
`size(given) = 0` and nothing to destroy. *(i) Lower bound.* Every change
moves the size by exactly one: up for the two additions, down for a removal
or an identification (`Step7.size_step`; 6:D8's `Step6.size_step` through
the naming map for the three kinds that need a term — `Seed.Fourth.
size_addAssertion`, `Seed.Fifth.size_remove`, `Seed.Fifth.size_identify` on
the named state — and `size_addTerm7`, re-proved without names, for the term,
since the empty state cannot be named). So a state reached from the empty
state in `n` changes has size at most `n` (`Reach7.size_le`,
`fewest_changes7_lower`). *(ii) Upper bound.* From the empty state add one
term of the target; the target then contains the one-term state, and the
sixth's addition path reaches it in the size difference
(`reach7_of_contains`: 6:D8's `reach6_of_contains` through the naming map,
both names on the added term); together `reach7_by_additions`: every
well-formed state is reached in exactly its size. If the target has no term
it is the empty state (`eq_empty_of_wf`) and zero changes do. Both bounds:
`fewest_changes7`; the one-term state costs one (`cost_oneTerm`). *(iii)
Every writing.* Changes commute with one-to-one rewriting (D7) and the size is
the same in every writing (`size_rename7`), so the fewest changes to a result
is the size of any of its writings (`fewest_changes7_every_writing`; target 5
of the plan closed). *(iv) Which changes raise the cost by exactly one.* The
additions, and nothing else (`Step7.lowers_or_adds`; computed:
`code/seventh/cost.py` `raises_by_one` agrees with the outcome on every
change within the bound of every run, `cost_rule_disagreements` empty,
`size_not_moved_by_one` empty; 190 936 changes in the 5-term run). *(v)
Parity.* The size and the length of a sequence have a fixed parity
(`Reach7.size_parity`, 6:D8(v) re-proved); no change keeps the round
(`changes_keeping_the_round: 0` in every run). *(vi) Every shortest sequence
is additions only.* A sequence from the empty state whose length is the size
of its end contains no removal and no identification: one would leave the
size below the length (`shortest_are_additions`, stated with the additions
as a sequence of their own, `AddReach7`). Computed: the round of every
explored result equals its size in all three runs and the census
(`round_equals_cost_formula_for_every_result`), and every change that raises
the round is an addition (`count_shortest_sequences` checks it on every
change it follows).

**D5. Everything well formed is a result, the empty state included.** Every
well-formed state is reached from the empty state (D4(ii)), and every reached
state is well formed (`Reach7.wf`): `result7_iff`; the empty state is the
result of round 0 (`empty_is_a_result`). **The sixth's results are the
results with a term.** Every result of the sixth seed, from either beginning,
is a result of the seventh with its names forgotten (`results_forget_A`,
`_B`); every result of the seventh with a term is a result of the sixth from
either beginning once its names are placed on any of its terms
(`results_name`; 6:D9's `result6_iff_A`, `_B` through the naming map); and
the empty state is a result of the seventh that no sequence of the sixth
reaches (`sixth_never_empty`, `empty_is_new`; 6:D6's `Reach6.nonempty`). So
6:D9 survives as "the results with a term". Computed on every run and the
census (`compare_with_sixth`; 6:K1, 6:K2 computed again): under any
rewriting, the results with a term whose sixth-seed cost is within the
sixth's rounds are exactly the sixth's results at the same bound on terms —
7 177 without `bra` and 11 018 with it at 5 terms and 7 sixth rounds — and the
sixth's round of each is its sixth-seed cost formula
(`sixth_round_is_its_cost_formula_on_every_shared_result`); with the names
kept, the sixth's 25 197 and 30 010 results with their names forgotten are the
same 7 177 and 11 018 states, all of them results here, and every result with a
term and small enough size is among them. The independent counts agree too:
the sixth's counts of all well-formed states with `n ≥ 1` terms by total
multiplicity (13, 924, 49 357, 1 278 844, 15 677 058 for `n = 1 … 5`, 6:K1) are
this derivation's, with 1 for `n = 0` (K1).

**D6. What every result has.** Every result is well formed and finite
(`Reach7.wf`); a result other than the empty state has a term (D2). Nothing
else is kept (N6).

**D7. Changes commute with one-to-one rewriting; sequences keep their
length; the empty state is its own only writing.** `rename7` is the fourth's
`rename4` with the names left out; naming and then rewriting is rewriting and
then naming (`rename4_name`, definitionally), so 4:D11's and 5:D11's
commutation lemmas (`rename4_addTerm`, `rename4_addAssertion`,
`rename4_remove`, `rename4_identify`, no change) give the seventh's by
forgetting the names (`rename7_addTerm`, …, `rename7_identify`), and
`Step7.rename`, `Reach7.rename`, `size_rename7`, `rename7_empty` follow
(6:D11 through the maps).

**D8. Reachability: a term decides.** A well-formed state `t` is reachable
from a well-formed state `s` exactly when `t` has a term or `s` is empty:
`reach7_iff`. Necessity is D2. Sufficiency (`reach7_of_nonempty`): with both
`s` and `t` having a term, put both names on a term of `s` and on a term of
`t`; the sixth's criterion (`reach6_of_names`, 6:D12) then applies with
nothing to check, since the names of a named state are one term at both
ends, and its sequence — remove everything, identify every other term into
the named one, add what the target has — forgets to a sequence here. From the
empty state additions reach everything (D4(ii)). So the sixth's criterion
survives on states with a term as "always" (`criterion_survives`) and the
empty-state clause is new. Computed: the criterion agrees with a search along
the changes among the results within 3 terms and 8 rounds on every ordered
pair of the 89 results within 3 terms and 6 rounds (7 921 pairs; 7 833
reachable; the 88 unreachable are those into the empty state), and the
sixth's criterion (`code/sixth/reach.py`, without names) agrees with this
one on every pair of results with a term (7 744 pairs; 6:K8 computed again).

**D9. Reachability is mutual among the results with a term, one-way out of
the empty state; any two results are comparable; every result with a term
reaches itself in two changes.** `reach7_symm`, `reach7_total`,
`empty_never_returned`; the two-change cycle (`cycle2_7`, 6:D13's `cycle2_6`
through the naming map: add `xry` and remove it, or add a term and identify it
back), so the lengths of the sequences reaching a result with a term are
unbounded (`Reach7.cycles`, `Reach7.unbounded`) and infinitely many sequences
reach it; the empty state has no cycle (`no_cycle_at_empty`) and is reached by
one sequence, the empty one. One-way reachability among the results with a
term is refuted (`no_return_fails7`, `antisymm_fails7`, `length_not_unique7`:
the one-term and two-term states asserting nothing reach each other in one
change each way). Computed: every result but the empty state has a two-change
cycle in every run (`results_with_a_two_change_cycle = results − 1`); 3 828
unordered pairs of different results reachable both ways among the 88 results
with a term of the reachability run — all of them.

**D10. Within the bound the exploration is complete; the frontier is exact;
the shortest-sequence counts are exact.** *Completeness.* Let the bound be
`N` terms and `R` rounds. Every well-formed state with at most `N` terms and
size at most `R` lies at the end of the sequence of D4(ii), whose states never
have more terms than the target and whose size rises by exactly one at each
change; so every state on it is within the bound and, by induction along it,
found by the exploration in round = size. Every explored state is a
well-formed state within the bound by construction. The results with `n`
terms and total multiplicity `t` are counted independently by the sixth's
orbit method with the diagonal pairs among the cycles (6:D14, no change:
`count_free` mentions no name), with `n = 0` giving the empty state alone
(`code/seventh/orbits.py`); the explored counts by (terms, total) equal the
independent counts restricted to `n + t ≤ R` in every run and the census
(`explored_equals_independent_count`), and the counts agree with a listing of
every writing for small `n` and `t` (`tests/test_seventh_orbits.py`).
*Frontier.* An attempt leaves the bound on terms exactly when it is "add a
term" on a result with `N` terms: one entry per such result whose changes
were attempted (`frontier_entries_are_1_per_state_with_N_terms` true in
every run); the results of round `R` are the second part. *Shortest
sequences.* A shortest sequence is additions only (D4(vi)), so it never has
more terms than its target and the count is exact for every result within
the bound (`results_with_exact_sequence_count = results` in every run; the
sixth's clauses about the names have no object). *Rounds.* The number of
results of round `r` without any bound is the number of well-formed states of
size `r`, `Σ_{n ≤ r} count(n, r − n)` (`layer_counts`); a result of round `r`
has at most `r` terms, so rounds `0 … N` of a run within `N` terms agree with
it (`rounds_agreeing_with_unbounded_formula` true in every run; 6:D14's "`N −
2`" becomes `N`, since nothing is given).

**D11. Two terms: the results of every round in closed form.** With at most
two terms the results of round `r` are: the empty state (`r = 0`); the
one-term state with `ara` `r − 1` times (`r ≥ 1`); and, with two terms, the
four multiplicities `(p, i, j, q)` of `ara`, `arb`, `bra`, `brb` summing to
`t = r − 2`, up to the swap `(p, i, j, q) ↔ (q, j, i, p)`: the compositions
of `t` into four parts, `C(t+3, 3)`, plus the ones the swap fixes (`p = q`,
`i = j`, so `t` even: `t/2 + 1` of them), halved —
`(C(t+3, 3) + [t even](t/2 + 1)) / 2`. Total `1, 1, 2, 3, 7, 11, 20, 29, 45,
61, 86, 111, …`: cubic, so 100 rounds would hold about 2.1 million results.
Proof: the cost of each state with at most two terms is its size (D4), and
the count of two-term states of a given total is the orbit count under the
one non-trivial rewriting. Computed: `two_term_rounds_equal_closed_form` true
on all 40 rounds of the two-term run, and the closed form equals the
independent count for every total up to 12 (`two_term_closed_form_mismatches`
empty). **One-term results** are reached by exactly one shortest sequence (a
term, then `ara` `k` times: `one_term_results_have_one_shortest_sequence`
true in every run); for two or more terms the counts are computed per result
(K7; O1).

**D12. The two readings of sameness coincide.** The earlier derivations read
"differ only in how their terms are written" two ways: any rewriting (FREE),
or rewritings keeping the writing of `a` and of `b` (ANCHORED, 1:C4). With no
`a` and no `b` there is nothing to keep: every rewriting keeps the names, so
the rewritings allowed under the second reading are all rewritings and the
two readings give the same least writing and the same results. Not in Lean
(the ANCHORED reading was never formalised as a reading; `rename7` is the
one rewriting); the proof is this paragraph, and it is the reason there is
one exploration per bound instead of the sixth's four. Computed as a
consequence: the sixth's ANCHORED results with their names forgotten are
exactly its FREE results (D5: 25 197 named results forget to the 7 177
unnamed ones at 5 terms and 7 sixth rounds).

**D13. What the sixth's cost becomes.** The sixth's fewest changes,
`size − size(given) + 2·lost`, measured from `arb`, does not survive: the
one-term state asserting nothing is one change from the empty state, while
under the sixth seed its named form has potential 5 and costs two changes
from `arb` (`sixth_cost_fails`; 6:D8's `costA6`, `fewest_changes6_lower_A`
through the naming map); the sixth's beginnings themselves cost 3 and 4
changes from here (`given.json`). Without `bra` the sixth's cost has the
other parity from the seventh's and equals it on no result
(`results_where_the_sixth_cost_equals_the_cost: 0` in every run); with `bra`
the two agree on a few results (19 of 22 685 at 5 terms), by coincidence of
the numbers. What survives is the size difference (4:D8's, 6:D8's cost on
states containing what is given) with `size(given) = 0`
(`size_difference_survives`).

**D14. Nothing about the asserting holds in every result.** By D5 every
well-formed state is a result, so a statement holds in every result exactly
when it holds in every well-formed state; of the eighteen statements tested
(§6) each fails in some well-formed state — "at least one term" in the
empty state, the rest in the results the sixth already had — and each holds
in some (ten of them in the empty state itself, vacuously). Computed:
`statements_holding_in_every_result` is empty in every run.

**D15. The unchosen reading of identification.** Under the reading in which a
merged multiplicity is the *larger* of the parts instead of their sum, the
results are the same (every well-formed state: D4(ii) identifies nothing), the
reachability criterion is the same (D8's sequence identifies terms only in
states with nothing asserted at all, the sixth's), and the cost is the same
(D4(i) needs only that a change moves the size by at most one, which the
larger-of-the-two reading also gives: an identification then lowers the size
by one or more). So the two readings agree on everything computed here; the
sixth's D19 (the readings differ in cost with `bra` given) has no object
without `bra`. Not in Lean; the proof is this paragraph.

## 5. What does not follow

Each item has two witnesses among the results, or a proof.

**N1. Anything about the asserting**, and by D5 that is anything about
which assertions are asserted and how often that is not true of every
well-formed state: every one of the eighteen statements tested holds in some
result and fails in another in every run (`statements_that_do_not_follow`,
`follows_*.csv`). The sixth's one everywhere-true statement, "at least one
term", fails in the empty state, round 0; "no terms and nothing asserted"
holds in the empty state alone.

**N2. That there is a term; that there are exactly two, or at least two.**
The empty state has none (round 0); the one-term state has one (round 1);
the two-term state has two (round 2); the three-term state three (round 3).

**N3. Growth.** Nothing forces terms or assertions to be added or to stay:
what is given adds none; every result of round `r ≥ 1` has a change that
lowers its size (a removal or an identification, 6:N7 through the maps), and
every result has a change that raises it. Every result is finite (D6); every
round has a new result (D11).

**N4. That a result is reached by one sequence only, or by finitely many;
that results of one round are reached by equally many shortest sequences.**
Every result with a term is reached by infinitely many sequences (D9). The
empty state, the one-term states and the states asserting nothing are
reached by one shortest sequence each (the terms, in one order); `a b; bra` by
two (`arb` or `bra` on the two-term state asserting nothing, the same result);
`a b; brb` by three; `a b c; crb` by eight (column
`shortest_sequences_of_changes`; 16 of the 22 686 results of the 5-term run
have one shortest sequence, 42 of the 56 111 two-term results).

**N5. That the number of changes of a result is the same for results of one
round with equally many terms.** It is `C(n, 2) + d + 1 + n²` (D3) and depends
on `d`: 6 for `a b; nothing asserted` and 7 for `a b; bra`, both with two
terms; 3 for `a; nothing asserted` and 4 for `a; ara`, both with one term.

**N6. That a multiplicity never falls; that the number of terms, the total
multiplicity, the size, or the fewest classes of a split never falls; that no
`xrx` stays asserted.** All refuted by witnesses, as 6:N13 (through the
maps). Computed: in the 5-term run 42 563 changes lower the number of terms,
29 602 a multiplicity, 72 165 the size, 1 161 the fewest classes (between
results asserting no `xrx`), and 12 783 make some `xrx` asserted on a result
asserting none (`changes_lowering`).

**N7. That a state is contained in its outcome; that a sequence of changes
carries every assertion somewhere.** Refuted, as 6:N14: the one-term state
asserting `ara` once and its removal (one change each way).

**N8. The sixth's notions of `bra`, the names, the given assertion and the
destroyed givens.** Without object: the seed names nothing and gives nothing.
The sixth's N1 and N2 (`bra`, not `bra`), its C2′, its D1 (`a ≠ b` to begin
with), its D7 (the names once one term stay one term) and its D8's destroyed
givens have nothing to refer to (§8).

**N9. That reachability among the results with a term is one-way, or that
two results are incomparable.** Refuted and derived respectively (D9).

**N10. That the beginning is returned to, or has a cycle.** Refuted (D2):
the empty state is the one result with no two-change cycle and the one
result not reached from every result.

**Refuted** (each a proved impossibility): a change other than adding a term
on the empty state (R1, D1); a sequence from a state with a term to the empty
state, or a non-empty sequence from the empty state to itself (R2, D2); a
sequence of changes to a result shorter than its size (R3, D4); a well-formed
state that is not a result (R4, D5); a change that keeps the size, or the
round, where it was (R5, D4(v)); a shortest sequence containing a removal or
an identification (R6, D4(vi)); two results with a term that do not reach
each other, or two results neither of which reaches the other (R7, D9); a
rewriting barred by the names — the two readings of sameness differing (R8,
D12); the sixth's cost as the fewest changes here (R9, D13); a result reached
by no sequence at all (R10, D5).

## 6. The exploration

**Protocol.** From the empty state, under the one reading of sameness: round
by round, every change on every result first reached in the round before
(C6), each result's changes fewest additions first — identifications (each
unordered pair once), removals (each asserted pair once, diagonal pairs
included), a term, then every ordered pair as an addition, `xrx` included,
asserted already or not (`C(n, 2) + d + 1 + n²` changes, every one performed;
one on the empty state). Each attempt records whether its outcome asserts
some `xrx` while the state asserts none (the sixth's record, kept for the
comparison). Three explorations (C8′): the main run (5 terms, 11 rounds), a
deeper run (3 terms, 14 rounds), and the two-term run (40 rounds). Beside
every run and the census the sixth derivation's explorations are made at the
same bound on terms with four rounds fewer, from both its beginnings and under
both its readings, and compared on the results with a term (D5). Files per run
(`evidence/seventh/`, tag `bound{N}_rounds{R}`): `results_*.csv` (one row per
result: terms, assertions counted and asserted, largest multiplicity, largest
`xrx` multiplicity, terms and assertions added to what is given, round, cost
by formula, fewest classes where no `xrx` is asserted, changes, additions,
changes making some `xrx` asserted, whether its changes were attempted,
shortest sequences and whether the count is exact, whether it has a term,
whether it reaches what is given and is reached from it, whether it asserts
nothing twice, whether it asserts no `xrx`, whether it is a result of the
sixth seed and the sixth's cost of it from either beginning),
`added_*.csv`, `frontier_*.csv`, `rounds_*.csv`, `follows_*.csv`;
`reach_bound3_rounds6.csv`; the full attempt log `attempts_bound2_rounds4.jsonl`;
`counts.csv`, `given.json`, `summary.json` (every check, per run),
`lean_axioms.txt`, `MANIFEST.sha256`.

**Results within the bound** (K1, K2). Every check of every run passes
(`summary.json`; `python code/generate_seventh.py` prints one line per run).

| run | results | by terms | asserting some `xrx` | shortest sequences (total) | the sixth's results among them (no `bra` / `bra`) |
|---|---|---|---|---|---|
| 5 terms, 11 rounds | 22 686 | 1 / 11 / 365 / 4 146 / 10 783 / 7 380 | 17 670 | 2 281 479 967 | 7 177 / 11 018 (7 sixth rounds) |
| 3 terms, 14 rounds | 29 191 | 1 / 14 / 924 / 28 252 | 27 046 | 71 513 837 362 | 16 258 / 23 273 (10) |
| 2 terms, 40 rounds | 56 111 | 1 / 40 / 56 070 | 55 709 | about 1.3 · 10^23 | 50 729 / 54 625 (36) |
| census, 6 terms, 12 rounds | 82 749 | 1 / 12 / 511 / 8 236 / 31 786 / 31 412 / 10 791 | 64 527 | — | 24 559 / 41 302 (8) |

In every run the results with a term whose sixth-seed cost is within the
sixth's rounds are exactly the sixth derivation's results at the same bound
(6:K1, 6:K2 computed again), each at the round the sixth's cost formula gives,
and the sixth's results with the names kept forget to the same states. Every
count by terms and total multiplicity equals the independent count
(`explored_equals_independent_count`, D10), and every result's round is its
size (D4).

**Rounds** (K2). 5 terms (`rounds_bound5_rounds11.csv`): new results per
round 1, 1, 2, 4, 10, 24, 64, 177, 516, 1 563, 4 869, 15 455; of which
asserting no `xrx` 1, 1, 1, 2, 4, 9, 20, 53, 138, 393, 1 118, 3 276; without
any bound on terms 1, 1, 2, 4, 10, 24, 65, 180, 530, 1 629, 5 226, 17 412
(`layer_counts`; rounds 0–5 agree with the run, as every round up to `N`
must). 3 terms: 1, 1, 2, 4, 9, 21, 51, 119, 267, 581, 1 176, 2 291, 4 237,
7 539, 12 892 (rounds 0–3 agree). Two terms: the closed form of D11 on all
40 rounds. Every round of every run has a new result.

**Attempts** (K3). 192 540 changes attempted in the 5-term run, 12 783 of
them making some `xrx` asserted on a result asserting none (the number the
sixth's function gives on the same results, D3); 1 in round 1 (the term), 3
in round 2 (a term, `ara`), 12 in round 3. The totals equal
`C(n, 2) + d + 1 + n²` summed over the results whose changes were attempted,
in every run. Of the 190 936 changes within the bound of the 5-term run,
118 771 raise the round by one and 72 165 lower it by one; none keeps it
(D4(v)). 785 407 changes attempted in the census.

**Frontier** (K5). Every result with `N` terms whose changes were attempted
has one entry (the term): 1 604 in the 5-term run, 15 592 in the 3-term run,
50 730 in the two-term run, 1 953 in the census. The second part, the results
of the last round whose changes await: 15 455 results with 483 162 changes
(5 terms), 12 892 with 232 689 (3 terms), 5 341 with 51 841 (2 terms), 58 110
in the census.

**Results by what they add to what is given** (K6;
`added_bound5_rounds11.csv`). A result of round `r` adds `n` terms and `r − n`
assertions, `n = 0 … min(r, 5)`: one result adds (0, 0) (the empty state),
one adds (1, `k`) for each `k` (the one-term states), `(C(t+3, 3) + [t
even](t/2 + 1)) / 2` add (2, `t`) (D11: 1, 2, 6, 10, 19, 28, 44, 60, 85, 110
for `t = 0 … 9`), and so on; nothing is ever negative, since nothing is given
to lose.

**Statements** (K7; `follows_*.csv`). Eighteen statements tested (the sixth's
seventeen unnamed ones and "no terms and nothing asserted"); none holds in
every result (N1). First failing rounds: at least one term 0; every term has
some `xry`, every term mentioned, no terms and nothing asserted 1; any two
related, no `xrx`, nothing asserted, both ways never 2; nothing twice, both
ways always 3; passes on 4; equal multiplicities, both ways equal 5; the
statements that fail in the empty state (exactly two terms, something
asserted, at least one term, at least two terms, some `xrx`, something twice)
0. Ten statements hold in the empty state, eight fail there.

**Reachability within 3 terms and 6 rounds** (K8; `reach_bound3_rounds6.csv`,
`summary.json` `reachability`), along the changes among the results of 3
terms and 8 rounds (475 results): 89 results (88 with a term, 61 asserting
some `xrx`); 7 921 ordered pairs, 7 833 reachable, 88 unreachable — exactly
the pairs into the empty state; 3 828 unordered pairs of different results
reachable both ways — every pair of results with a term; the criterion agrees
with the search on every pair; the sixth's criterion agrees on every one of
the 7 744 pairs of results with a term.

**Census** (6 terms, 12 rounds, counts only): 82 749 results (1 / 12 / 511 /
8 236 / 31 786 / 31 412 / 10 791 by terms); 785 407 changes attempted, 47 759
making some `xrx` asserted; the sixth's 24 559 and 41 302 results (8 sixth
rounds) are the results with a term of sixth-seed cost at most 8; every check
passes.

**Independent counts** (K1; `counts.csv`): all well-formed states with `n ≤
6` terms by total multiplicity `0 … 12`, up to rewriting: 1, 13, 924, 49 357,
1 278 844, 15 677 058, 99 876 431 for `n = 0 … 6`; beside them the number of
those asserting no `xrx` (the fifth's and sixth's count of legal states) and,
with two terms, the closed form of D11. The sixth's counts by destroyed
givens, from either beginning under any rewriting, add up to these for every
`n ≥ 1` (`sixth_counts_by_destroyed_givens_add_up_to_these`; 6:K1 computed
again).

**What is given** (`given.json`): the empty state, size 0; its one change,
a term, performed; its one result after one change, `a; nothing asserted`;
it reaches the one-term state, which does not reach it; it has no two-change
cycle; the one-term state costs 1 here (2 and 3 under the sixth seed, from its
two beginnings) and `a; ara` costs 2; the sixth's beginnings `a b; arb` and
`a b; arb bra` cost 3 and 4 from here (0 there); the empty state has no cost
under the sixth seed.

**Reproducibility** (K9, K10). `python code/generate_seventh.py` rewrites
every computed file of `evidence/seventh/` (about eleven minutes here, 20 MB);
`--check` regenerates into a temporary folder and compares byte for byte
(matched); `MANIFEST.sha256` lists every file's hash. `python
code/lean_report_seventh.py` builds all seven Lean libraries and rewrites
`evidence/seventh/lean_axioms.txt` (118 theorems, every one within
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit` or declared
axiom in `lean4/`). After this work the six earlier derivations' `--check`
and Lean reports were re-run (`paper/seventh/change_log.md`, item 12). Tests:
see `claim_ledger.md` K10; line and branch coverage of all of `code/` above
the gate, every evidence module fully covered (`python code/xry/gate.py
coverage.json`); `mypy --strict` clean; the prose watchlist clean, with every
pinned hit of this paper in §10.

## 7. What survives with nothing given

The task asks whether the results, the reachability criterion, the cost, and
the notions of names, given and separability survive. In one line each, with
the Lean statements of `Seventh/Compare.lean`:

- **The results extend by one.** Every result of the sixth seed is a result
  of the seventh with its names forgotten (`results_forget_A`, `_B`); every
  result of the seventh with a term is a result of the sixth once named
  (`results_name`); the seventh has exactly one result no sixth sequence
  reaches, the empty state (`empty_is_new`). So the sixth's set survives as
  "the results with a term", and the results are every well-formed state
  (`result7_iff`).
- **The reachability criterion survives on states with a term and gains a
  clause.** There the sixth's names criterion says "always" through the
  naming map and so does the seventh's (`criterion_survives`); the empty state
  reaches everything and is reached by nothing else (`reach7_iff`,
  `empty_never_returned`). Mutual reachability, comparability and the
  two-change cycle stay (D9).
- **The cost does not survive; the size does.** The sixth's fewest changes
  measured from `arb` is no bound here (`sixth_cost_fails`: one change where
  the sixth's potential says two); the fewest changes is the size, the
  fourth's and sixth's size difference with `size(given) = 0`
  (`size_difference_survives`, `fewest_changes7`). Parity survives; the
  changes that raise the cost are now exactly the additions.
- **The names have no referent.** Through the naming map every state's names
  are one term, so every statement the sixth made about the names holds
  vacuously or says nothing (`names_merged_vacuous`); the two readings of
  sameness they told apart coincide (D12); the naming map itself is what
  lets the sixth's proofs be cited.
- **The given has no referent.** What is given is the empty state: a result
  (round 0), the beginning of every sequence, never returned to (D2); the
  sixth's `bra` alternative, destroyed givens and containment of the given
  have no object.
- **Separability**, read as telling the two named terms apart — the sixth's
  one-way property, "the names once one term stay one term" — has nothing to
  apply to. What replaces it is the seventh's one-way property: having a
  term. Read instead as the fewest classes of a split with no two related
  terms in a class, it survives as a function of a state asserting no `xrx`
  (0 on the empty state) and, as under the sixth, can fall along a change
  (N6).

## 8. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| a beginning other than the empty state | eliminated by the seed (G3″: nothing is given); every well-formed state is a result of the empty one (D5) |
| FREE / ANCHORED sameness | one reading: the two coincide with no names (D12); nothing is computed twice |
| identification: multiplicities add up / the larger of the two | the first chosen and computed; the second kept as an alternative with the same results, reachability and cost (D15) |
| the other orders of attempts | not computed; same results and rounds (D4) |
| a bound on terms alone | eliminated: the results within it are infinite (D5) |
| every well-formed state within the bound, up to sameness | kept; none dropped (D10) |

Earlier results that fail, or lose their object, under the seventh seed, each
with the reason: 6:C2′, 6:N1, 6:N2 (`bra`) — without object; 4:D1, 1:D1 (`a ≠
b`), 6:D1 — without object, no names; 6:D2 (the beginnings) — without object;
6:D7 (the names once one term stay one term), 1:D7 — vacuous through the
naming map (`names_merged_vacuous`), replaced by D2; 6:D8 (the cost with
destroyed givens), 5:D8, 1:D8 — do not survive, `sixth_cost_fails`; the size
difference (4:D8) survives with `size(given) = 0`; 6:D12 (the names
criterion) — survives on states with a term as "always", the empty-state
clause added (D8); 6:D9 (the results are every well-formed state with a
term) — extends by one result, the empty state (D5); 6:D14's exactness
clauses about the names, and its "rounds `0 … N − 2`" — replaced by "exact
everywhere" and "rounds `0 … N`" (D10); 6:D17 (two-term counts with the
names kept, cubic) — replaced by D11's form; 6:D19 (the two readings of
identification differ in cost with `bra`) — without object, the readings
agree (D15); 6:N3's "at least one term" among the everywhere-true
statements — fails at the empty state (N1); 6:N5, 6:N15 (what is given
survives) — without object; the sixth's `merged_optimal`, `lost_free`,
`lost`, `raises_by_one`, `count_named`, `counts_by_lost`, `two_term_round_count`
— about the names or the given, not imported (`change_log.md`, item 3); every
K-claim of the sixth — computed again on the results with a term (§6).
Everything else cited stands with the re-check given at its citation.

## 9. Open

- O1. A closed form for the number of shortest sequences reaching a result
  with two or more terms: computed per result within the bound (K7), exact
  there (D10); with one term it is 1 (D11). The least-writing identification
  of `arb` with `bra` on the two-term state makes the count differ from a
  count of arrangements.
- O2. Results beyond the declared bounds, listed: the frontier is exported
  (both parts); the census counts at 6 terms; the seed's 100 rounds with two
  terms are given in closed form (D11), not listed.
- O3. Lean statements of D10's completeness, of D11's closed form, of D12
  (the coincidence of the two readings of sameness) and of D15: proved in
  the paper and checked by computation.
- O4. The earlier papers' O1 (multiplicity) stays closed by the fourth seed;
  their O2 (the number of new results beyond the bound) is given by the
  series and the size for any round (D10, `layer_counts`) and not listed.

## 10. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Directed multigraphs with loops, unlabelled, under vertex insertion,
  vertex identification, and edge insertion and deletion, generated from the
  empty graph.** D5 is that every finite such multigraph is generated, and
  D8 that the edit graph on them is strongly connected except for the empty
  graph, which is a source: contraction never removes the last vertex.
- **Graph edit distance from the empty graph.** D4 is the observation that,
  with unit cost per edit and contraction allowed, the edit distance from the
  empty multigraph to any multigraph is its number of vertices plus its
  number of edges (with multiplicity), attained by insertions alone — the
  potential-function argument of the first derivation with no marks to
  destroy.
- **Pólya enumeration.** The independent count (D10) is the sixth's
  cycle-index computation with the empty vertex set added; D11 is the case of
  two vertices, where the only non-trivial rewriting is the swap and the
  count of two-term states of a given total is the average of the number of
  compositions into four parts and the number the swap fixes.
- **Free generation.** That the first move from nothing is forced (D1), that
  nothing about the generated structure is forced (D14) and that every
  structure is reached (D5) is the statement that the four operations
  generate all finite multigraphs from the empty one, with the vertex count
  as the one quantity that only insertion raises and only contraction lowers
  and that never returns to zero (D2).

What appears to be specific to this seed: that removing the given removes
every asymmetry the earlier derivations found — no obstruction (sixth), no
names, no destroyed givens, no `bra` — and leaves exactly one: the empty
state, which every sequence starts from and none returns to; that the cost
collapses to the size and the shortest sequences to additions alone
(`shortest_are_additions`), while the reachability criterion keeps its shape
with "has a term" in place of "the names are one term"; and that the sixth
derivation's results, criterion, counts and change counts are recovered
exactly on the results with a term through two definitional maps
(`Seventh/Compare.lean`), the whole difference being one state.
