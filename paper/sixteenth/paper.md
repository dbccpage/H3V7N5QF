# What follows once a recorded leftover feeds back into the state

Sixteenth derivation. Input: `prompt/sixteenth/seed_prompt.md`. Task:
`prompt/sixteenth/prompt.md`. Claim IDs refer to `paper/sixteenth/claim_ledger.md`;
an ID written `9:D4` refers to the ninth derivation's ledger
(`paper/ninth/claim_ledger.md`), `14:D5` to the fourteenth's
(`paper/fourteenth/claim_ledger.md`). Lean names in the namespace
`Seed.Sixteenth` are in `lean4/Sixteenth/`; names in `Seed.Ninth` and
`Seed.Fourteenth` are the ninth's and the fourteenth's. The axiom report for
every theorem cited here is `evidence/sixteenth/lean_axioms.txt`. Computed
files are in `evidence/sixteenth/`, written by `python code/generate_sixteenth.py`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Where a result of an earlier derivation is used it is cited and re-checked
from the sixteenth seed, and the re-check says whether the result *survives
once the record feeds back*. The re-check is one of: *(no change)* the
statement mentions no record; *(through the maps)* a sixteenth state projects
to a ninth state (`RSt.toNDSt`, the record forgotten) and a ninth state embeds
as a sixteenth state with an empty record (`NDSt.ofRSt`), every change of the
sixteenth projecting to a change of the ninth (`Step16.proj`) and every
addition or identification of the ninth embedding (`Add9.embed`,
`Step9.embed_identify`) — but a removal of the ninth embeds only into a state
carrying one recorded leftover (`Step9.embed`); *(re-proved)* proved afresh for
states with a record; *(computed again)* the sixteenth exploration compared
with the ninth's at the same bound on the results with an empty record.

A claim of the tenth to fifteenth derivations that held *by construction*
because the record sat off the result is re-examined here (§9): the record is
now in the state, so "not a third multiplicity, not an assertion, not a change"
are no longer free.

## 0. Findings in brief

1. The sixteenth seed is the fourteenth with one sentence changed: a recorded
   leftover `xℓy` may be admitted, adding the assertion `xry` or the assertion
   `xsy`; an unadmitted leftover is not an assertion. The unadmitted leftovers
   must therefore be carried by the state (C-R1): a state is a ninth state
   together with its *record*, a count of unadmitted leftovers per ordered
   pair; an admission is a change of the fourth kind (adding an assertion),
   performed by admitting.
2. **Removing an assertion and admitting its leftover into the same relation
   is the identity** on the state, record included (D1, Lean
   `remove_admit_same`; 0 failures on the 7 494 removals checked within 3
   terms and 8 rounds). **Admitting it into the other relation is a result
   different from the start and from the direct addition** (D2,
   `remove_admit_other_ne`, `remove_admit_other_ne_direct`): its ninth state is
   the direct addition's (`remove_admit_other_st`); no *ninth* state is new —
   what is new is the pairing with an emptier record.
3. **The feedback does not terminate.** A removal followed by the admission of
   its leftover into the same relation is a two-change cycle at every state
   with an assertion (D9, `cycle2_assert16`, `admit_remove_unbounded`); a term
   added and identified away is one at every state with a term (`cycle2_16`);
   the record is unbounded (D7: the results of round `k` with one term number
   `(⌊(k−1)/2⌋+1)(⌈(k−1)/2⌉+1)`, every larger record in reach). A finite
   bound on terms and rounds is declared (C8′), the frontier exported, and
   completeness within it certified by an independent count (D8).
4. **The cost of a result is its potential, the ninth's size plus twice its
   record** (D3, `fewest_changes16`): a term, a direct assertion and a removal
   raise the potential by one, an admission and an identification lower it by
   one. **No shortest sequence from the empty beginning admits or identifies**
   (D4, `no_fall_on_shortest16`): an assertion that arrives by admission costs
   three changes where a direct addition costs one (`admission_costs_three`).
   The ninth's cost survives exactly on the results with an empty record
   (`fewest_changes16_of_empty_record`) and fails off them
   (`ninth_cost_fails_off_empty_record`: one term with one leftover recorded
   costs 3 against size 1).
5. **The mass — both totals plus the record — never falls** (D5,
   `Reach16.mass_le`), so the ninth's has-a-term criterion fails: `ara` once
   never returns to the one-term state asserting nothing
   (`has_term_criterion_fails16`), and reachability among the results with a
   term is one-way again (`one_way16`). What decides reachability is that the
   mass is *carried*: a result reaches another exactly when the first is empty
   or some map of its terms into the other's terms sends at most each pair's
   mass onto it (D6, computed: the criterion agrees with breadth-first search
   on all 27 889 ordered pairs of the 167 results within 3 terms and 5 rounds;
   the ninth's criterion admits 17 624 of those pairs and this seed refuses
   them, never the reverse).
6. **The results are every well-formed state** — a ninth state with any
   record over its terms (D8, `result16_iff`); the ninth's results are exactly
   those with an empty record, at the ninth's rounds and with the ninth's
   shortest-sequence counts (`results_ninth_iff16`, `ninth_round_survives`;
   computed again on 7 271 results). The count is the orbit count with a third
   factor `1 / (1 − x^{2L})` per cycle of pairs (D8): 10 697 results within 3
   terms and 8 rounds against the ninth's 7 271; it is not a product of the
   ninth's count and the record's (76 against 68 with two terms at weight 3).
7. **What survives** (§9): the ninth's results (as the empty-record results),
   jointly free results, the one-way exit from the empty state, the exchange
   symmetry, and the size as the cost on the empty-record results survive; the
   size as the cost in general, the has-a-term criterion, mutual reachability
   among the states with a term, and the add-then-remove cycle fail. Of the
   fourteenth: "leftover of `r` is leftover of `s`" survives and gains force
   (it is what admits an `r` leftover into `s`); "an unadmitted leftover is not
   an assertion" survives with that qualifier and no further; "clearing
   leftover is not one of the four kinds" fails (an admission clears a leftover
   and is a change of the fourth kind); "leftover is not a third multiplicity"
   is re-examined: the record is a count per pair in the state, but it is not
   a third relation — no addition raises it, only a removal does, and only an
   admission lowers it.

## 1. What the seed gives

| ID | Given |
|---|---|
| G1, G2⁗, G3″, G6, G7, G11–G14 | The sentences of the ninth seed, word for word (`diff` against `prompt/ninth/seed_prompt.md`) |
| G15′ | After every change, record what that change leaves. A leftover is written neither `xry` nor `xsy`. A recorded leftover `xℓy` may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion. |

The `diff` against `prompt/fourteenth/seed_prompt.md` replaces one sentence
("A leftover is not an assertion and is not an answer.") by the last of G15′;
nothing else changes.

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, assertion `xry` or `xsy`, multiplicity, empty beginning, four kinds | given (ninth) | the ninth state is the state part, `RSt.st` |
| a leftover recorded after every change, written neither `xry` nor `xsy` | given (G15′) | the fourteenth's writing, reused |
| a recorded `xℓy` may be admitted, adding `xry` or `xsy` | given (G15′) | the feedback |
| an unadmitted leftover is not an assertion | given (G15′) | the record is kept apart from the two multiplicity functions |
| the record: a count of unadmitted leftovers per ordered pair, carried by the state | chosen (C-R1) | the two unchosen readings C-R2, C-R3 kept and computed |
| an admission is a change of the fourth kind, performed by admitting; it consumes the leftover | chosen (C-R1) | refused alternatives in §3 |
| a removal records one leftover of its pair; additions record nothing | derived from G15′ + 14:C-F1 | `leftover_of16` |
| the merge writing of an identification is not admissible | derived (it is not written `xℓy`) | recorded on the change, as 14:C-F1 |
| an identification carries the record with the terms | chosen (C-R1) | the fifth's reading on the record |
| the potential `size + 2·record` as the cost | derived (D3) | Lean |
| the mass `Σ r + Σ s + record`, never falling | derived (D5) | Lean |
| the carrying criterion for reachability | computed (D6); necessity derived | Lean for the mass; search for the criterion |
| the results: every well-formed state; the count with a third factor | derived (D8) + computed | Lean, orbit count |
| the same-relation identity; the other-relation result | derived (D1, D2) | Lean |
| the feedback does not terminate | derived (D9) | Lean |
| the record as a third relation | refuted (D10) | not raised by any addition |
| the maps to and from the ninth: every change projects, additions and identifications embed, a removal embeds with one leftover recorded | derived (D13) | Lean |
| the exchange of the relations as a symmetry | derived (D12) | Lean |
| the criterion of the set reading C-R2 | open (O2) | neither the ninth's nor the carrying criterion |

## 3. Readings that had to be chosen

**C-R1 (chosen).** A state is a ninth state (9:C1′) together with its record:
for every ordered pair of its terms, how many leftovers `xℓy` are recorded and
not admitted. Each removal records one leftover ("record what that change
leaves" is said of every change, so two removals of a pair record two); an
addition records nothing (14:C-F1, kept); an identification's merge writing is
recorded on the change and is not admissible, since it is not written `xℓy`.
An *admission* of a recorded `xℓy` into `r` or into `s` is a change: it adds
the assertion, which is the fourth kind; it consumes the leftover, which is
then the assertion it added; it leaves nothing. The leftover names no relation
(14:D5), so a leftover left by a removal in `r` may be admitted into `s`. An
identification replaces both terms by one in the record as in every
assertion, the record of the merged pairs adding up (the fifth's reading,
9:C5⁗, applied to the record). Two results are the same when one rewriting of
the terms carries the two relations and the record together (9:C4 on three
functions). The attempt order, fewest additions first: identifications,
removals in `r`, in `s`, a term, the direct additions in `r`, in `s`, then
the admissions in `r`, in `s` (an admission adds an assertion and is listed
after the direct additions); the order fixes the log only, the rounds being
the potential (D3).

**C-R2 (unchosen, kept, computed).** The record is a set: a pair is recorded
or not, and a second removal of a recorded pair records nothing new. §10.

**C-R3 (unchosen, kept, computed).** An identification drops the leftovers
naming either merged term instead of carrying them. §10.

**Set aside, with the sentence that refuses each.** *Admission is not a
change*: it adds the assertion `xry`, and adding an assertion is one of the
four kinds (G6, G15′). *An admitted leftover stays recorded and may be admitted
again*: an unadmitted leftover is not an assertion, so an admitted one is the
assertion it added, and a second admission would add an assertion from no
leftover. *The merge writing is part of the result*: the fourteenth's C-F2,
cited (14:D12); it multiplies results by inert data that no change can act on,
and is not recomputed.

C3, C5⁗, C6, C8′, C9 of the ninth paper, unchanged in kind. Bounds used here
(C8′): 3 terms with 8 rounds; 4 terms with 7; 2 terms with 10; full attempt
logs at 2 terms and 3 rounds; reachability by search among the results of 3
terms and 5 rounds along the changes among those of 7 rounds; the unchosen
readings at 2 terms with 6 rounds, their reachability at 5 rounds along 8;
independent counts up to 4 terms and weight 8. Every run completes in seconds;
the seed's 100 rounds do not (the results of round 10 with two terms number
8 736, and every round is a level set of the potential, D3).

## 4. The same relation, and the other

**D1.** Removing `xqy` and admitting the leftover it records back into `q` is
the identity on the state, record included. Lean `remove_admit_same`: the
ninth state returns by `remove_add9` (the multiplicity rises to what it was),
and the record by lowering the count it had raised. Computed: on every
removal within 3 terms and 8 rounds — 7 494 removals among the 52 420
changes checked — the outcome of the admission is the state removed from
(`records.same_relation_not_identity` empty in every run); `given.json`
`same_relation`.

**D2.** Admitting the leftover into the other relation is a result different
from the start (Lean `remove_admit_other_ne`: the other relation's
multiplicity of the pair is one higher) and different from removing then
adding directly (`remove_admit_other_ne_direct`: the record differs by one
leftover); computed up to rewriting on every removal within the bounds
(`other_relation_same_as_start`, `other_relation_same_as_direct` empty). The
two outcomes have the same ninth state (`remove_admit_other_st`, by
construction). So no ninth state is new: every result's ninth state is a
result of the ninth (D8), and what admission into the other relation gives
is that ninth state *with an emptier record* — `ara` removed and admitted into
`s` is `asa` with nothing recorded, where removing then adding `asa` directly
is `asa` with `aℓa` recorded (`given.json` `other_relation`).

**D11.** A leftover left by a removal in `r` is admitted into `s`: on `arb`
and `asb` each once, removing `arb` records `aℓb`, which admitted into `s`
gives `asb` twice (Lean `r_leftover_admitted_into_s`, `given.json`
`the_fourteenth_witness`). The record of a removal does not depend on the
relation removed from (`record_names_no_relation`, by construction).

## 5. The cost

**D3.** The fewest changes from the empty beginning to a result is its
potential, the ninth's size plus twice its record. Lean: every change moves
the potential by exactly one — up for a term (`potential_addTerm`), a direct
assertion (`potential_addAssertion`) and a removal (`potential_remove`: the
multiplicity falls by one, the record rises by one), down for an admission
(`potential_admit`) and an identification (`potential_identify`; both totals
and the record are kept, one term is lost) — so a result reached in `n`
changes has potential at most `n` (`Reach16.potential_le`,
`fewest_changes16_lower`); and the empty state reaches every well-formed
state in exactly its potential (`reach16_by_additions`): the ninth's additions
to the ninth state (9:D4 through the embedding, `AddReach9.embed`), then an
addition and a removal for every recorded leftover (`reach16_record`). Both
in `fewest_changes16`. Computed: the round of every result is its potential
(`round_not_potential` empty in every run); every change within the bounds
moves the potential by exactly one in the direction its kind says
(`potential_not_moved_by_one`, `direction_mismatch` empty); the results of
round `k` within `N` terms, for `k ≤ N`, equal the unbounded count of the
states of potential `k` (`rounds_agreeing_with_unbounded_series`); the
potential and the length of a sequence have a fixed parity
(`Reach16.potential_parity`).

**D4.** No shortest sequence from the empty beginning admits or identifies.
Lean: a sequence counted with its *falls* (admissions and identifications,
`ReachD`) satisfies potential-at-the-end + 2·falls = length
(`ReachD.potential` from the empty state), so a sequence of length the
potential has no fall (`no_fall_on_shortest16`). Hence an assertion that
arrives by admission costs three changes (add, remove, admit) where a direct
addition costs one: `ara` is two changes from the empty state, four through
its leftover, and every sequence of length two to it admits nothing
(`admission_costs_three`; `given.json` `admission_costs_three`, the
potentials along the route `0, 1, 2, 3, 2`). Between results an admission
can be the only route: the identity of D1 is a state with a leftover reaching
the state without it, which no addition and no removal can do (the record is
lowered only by an admission, `record_moved_only_by_removal_and_admission`).

**What survives of the ninth's cost.** On the results with an empty record
the potential is the size, so the ninth's fewest changes survive there
(`fewest_changes16_of_empty_record`, `ninth_round_survives`); off them it
fails: one term with `aℓa` recorded costs three changes, its ninth size being
one (`ninth_cost_fails_off_empty_record`). Computed: `ninth_seed_cost_of_the_state`
equals `fewest_changes_by_formula` in `results_*.csv` exactly on the rows with
`nothing_recorded`.

## 6. The mass, and reachability

**D5.** The mass — both totals plus the record — never falls along a change:
a removal moves one unit from a multiplicity into the record (`mass_remove`),
an admission moves it back (`mass_admit`), an identification adds up
(`mass_identify`), a term leaves it (`mass_addTerm`), a direct assertion
raises it (`mass_addAssertion`). Lean `Step16.mass_le`, `Reach16.mass_le`.
Computed: `mass_fell` empty on every change within the bounds, and so is
`diagonal_mass_fell` (the mass on the pairs `(x, x)`; computed only, not in
Lean). Consequences in Lean: **the has-a-term criterion does not survive** —
`ara` once reaches the one-term state asserting nothing under the ninth seed
(9:D8) and never here, its mass 1 being above 0
(`has_term_criterion_fails16`); reachability among the results with a term is
**one-way** again (`one_way16`), where the ninth had it mutual (9:D9).

**D6 (computed; necessity derived).** A result reaches another exactly when
the first is empty, or there is a map of the terms of the first into the terms
of the second under which every pair of the second receives at most its own
mass (the *carrying* criterion, `sixteenth.reach.carries`). Why: along one
change the mass of a pair is kept by a removal and an admission, raised by a
direct addition, and added up over the merged pairs by an identification, and
a term is never lost except by merging; conversely such a map is realised by
identifying the terms it merges, adding the terms it misses, and then, pair by
pair, removing every assertion, adding the missing mass directly, removing it,
and admitting the wanted multiplicities. The computed form: the criterion
agrees with breadth-first search along the changes on every one of the 27 889
ordered pairs of the 167 results within 3 terms and 5 rounds
(`reach_bound3_rounds5.csv`, `summary.json` `reachability`); 10 099 pairs are
reachable, 17 790 not, 596 unordered pairs both ways. The ninth's criterion
admits 27 723 pairs (all but the 166 into the empty state); of them 17 624
this seed refuses, and it admits none the ninth refuses. The two mass
invariants alone (the mass and its diagonal part) admit 4 227 pairs the
criterion refuses — the criterion is finer than the invariants. In Lean: the
necessity through the mass (`Reach16.mass_le`), sufficiency from the empty
state (`reach16_by_additions`), from a state to the embedding of a ninth state
by admitting every leftover (`reach16_admit_all`), and the general sufficiency
not formalised (O3).

## 7. Termination, and the record's growth

**D9.** The feedback does not terminate: a leftover can be admitted and
re-removed without bound. Lean: removing an assertion and admitting its
leftover back is a cycle of two changes at every state with an assertion
(`cycle2_assert16`), so `ara` reaches itself in `2k` changes for every `k`
(`admit_remove_unbounded`); a term added and identified away is a cycle at
every well-formed state with a term (`cycle2_16`, through
`identify_addTerm16`), so the lengths of the sequences reaching a result are
unbounded (`Reach16.unbounded`). The ninth's add-then-remove is **not** a
cycle here — it leaves a leftover (`add_remove_ne`; its ninth state does
return, `add_remove_st`, the fourteenth's `add_remove`). Computed: every
result but the empty state has a two-change cycle
(`results_with_a_two_change_cycle` = results − 1 in every run), and the
ninth's add-then-remove on `ara` returns to `ara` with `aℓa` recorded
(`given.json` `cycles`).

**D7.** The record grows without bound: the one-term results of round `k ≥ 1`
number `(⌊(k−1)/2⌋ + 1)·(⌈(k−1)/2⌉ + 1)` — the triples `(α, β, γ)` with
`α + β + 2γ = k − 1` — computed and equal to the exploration in every run
(0, 1, 2, 4, 6, 9, 12, 16, 20, 25, 30 for `k = 0 … 10`), against the ninth's
`k` (9:D11). A finite bound is declared (C8′); the frontier is one entry per
result with `N` terms whose changes were attempted (1 573, 44, 6 729), the
attempt being the term; the results of the last round await their changes
(8 046 results with 190 340 changes; 2 332 with 56 754; 8 736 with 132 904).

## 8. The results and the count

**D8.** Every well-formed state — a ninth state with a record naming only its
terms — is a result (`result16_iff`); the ninth's results are exactly the
results with an empty record (`results_ninth_iff16`), at the ninth's round
(`ninth_round_survives`), and any two well-formed parts on the same terms with
any record on them make a result (`results_pair16`: jointly free, with the
record free too). The sixteenth has results no ninth sequence reaches
(`leftOne_is_new`). Computed again: in every run the results with an empty
record, read as ninth states, with their rounds and their shortest-sequence
counts, are exactly the ninth's at the same bound (`ninth_derivation` in
`summary_*.json`: 7 271 of 10 697, 2 301 of 3 033, 6 526 of 15 561) — a
comparison, not an identity, the sixteenth exploring a larger space along
more changes.

The count: the orbit method with the rewriting acting on all `n²` ordered
pairs three times — `1/(1 − x^L)` for `r`, the same for `s`, and
`1/(1 − x^{2L})` for the record, a recorded leftover weighing two — gives
the results by terms and weight (`counts.csv`); the explored results equal it
in every run (`explored_equals_independent_count`), which is the completeness
certificate within the bounds. Its record-free part is the ninth's count
(`empty_record_counts_are_the_ninth_counts`, 9:D10 recovered). Without a
bound on terms the results of round `k` number 1, 1, 3, 9, 33, 126, 534,
2 376, 11 285, 56 345, 294 522 (`k = 0 … 10`) against the ninth's 1, 1, 3, 8,
29, 104, 420, 1 783, 8 115, 38 813, 194 888. **The count is not a product**:
the ninth's count times the record's own count falls short from two terms on
(68 against 76 at weight 3, 216 against 248 at weight 4) and agrees for at
most one term, since one rewriting must fix all three functions at once.

**Attempts.** A result with `n` terms, `d_r + d_s` asserted pairs and `d_ℓ`
recorded pairs has `C(n, 2) + d_r + d_s + 1 + 2n² + 2·d_ℓ` changes, `2·d_ℓ`
of them admissions (`attempts_equal_formula`, `admissions_equal_formula` true
in every run; 53 993 attempts in the 3-term run, 1 472 admissions).

## 9. What of the earlier derivations survives

| Earlier result | Re-check | Verdict |
|---|---|---|
| 9:D4 fewest changes is the size | re-proved | survives on the empty-record results (`fewest_changes16_of_empty_record`), fails off them (`ninth_cost_fails_off_empty_record`); replaced by the potential (D3) |
| 9:D4(vi) every shortest sequence is additions only | re-proved | fails as stated (a removal raises the potential); survives as "no shortest sequence admits or identifies" (D4) |
| 9:D8 reachability is having a term | re-proved | fails (`has_term_criterion_fails16`); replaced by the carrying criterion (D6) |
| 9:D9 mutual among the states with a term; two-change cycle | re-proved | mutuality fails (`one_way16`); the cycle survives with other changes (`cycle2_16`, `cycle2_assert16`), the ninth's add-then-remove is no cycle (`add_remove_ne`) |
| 9:D2 the empty state is never returned to; a term stays | through the maps | survives (D13: `reach16_empty_iff`, `Reach16.nonempty`) |
| 9:D1 the first change adds a term | re-proved | survives (D13: `first_change_adds_term16`) |
| 9:D5 every well-formed state is a result; jointly free | re-proved | survives with any record (`result16_iff`, `results_pair16`); the ninth's results are the empty-record results (`results_ninth_iff16`) |
| 9:D10 the count, not a product | computed again | survives as the record-free part; the full count has a third factor and is again not a product |
| 9:D11 one-term results of round `k` number `k` | computed | fails; `(⌊(k−1)/2⌋+1)(⌈(k−1)/2⌉+1)` (D7) |
| 9:D16 the exchange is a symmetry | re-proved | survives (D12: `Step16.swap`, `exchange_symmetry16`; the record is unchanged by it) |
| 9:D3 changes per result | computed | survives with `+ 2·d_ℓ` |
| 14:D3 leftover is not an assertion | re-examined | survives of an *unadmitted* leftover only (G15′); an admitted one is the assertion it added (`admitted_leftover_is_the_assertion`) |
| 14:D5 leftover of `r` is leftover of `s` | by construction, now with force | survives (`record_names_no_relation`) and is what admits an `r` leftover into `s` (D11) |
| 14:D6 clearing leftover is not one of the four kinds | re-examined | fails: an admission clears a leftover and is a change of the fourth kind (`clearing_is_a_kind16`) |
| 14:D7 leftover is not a third multiplicity | re-examined | fails as stated: the record is a count per pair carried by the state (C-R1); it is not a third *relation* — no addition raises it (`record_not_raised_by_addition`), only a removal does, only an admission lowers it (`record_moved_only_by_removal_and_admission`) — and it is not an assertion (G15′) |
| 14:D9–D11 the ninth's cost, reachability, results survive under C-F1 | re-examined | the identity on states that carried them is gone; each is re-decided above |
| 14:C-F1 leftover on the change | partly kept | the merge writing and the writing of every change stay on the change (`writing_not_the_fourteenth` empty); the pair writing of a removal also enters the state |
| 15 admission of a *result* | without object | a different notion; the fifteenth's passage is not in this seed |
| 10–13 the record off the result, "by construction" | without object here | their seeds are unchanged; the sixteenth is the case where the construction does not apply |

## 10. The unchosen readings (D14)

**C-R2 (the record as a set).** At 2 terms and 6 rounds: 381 results against
386 (1, 1, 3, 8, 28, 84, 256 per round), equal to its own count (the third
factor `1 + x^{2L}`); the round of every result is still its potential; but
**the same-relation identity fails** — 10 removals within the bound, the first
on `a; asa; aℓa` removing `asa`: the pair being recorded already, the removal
records nothing new, and the admission then lowers the record below what it
was (`given.json` `set_reading`, `alternatives.json`). Its reachability is
neither the ninth's criterion (2 653 disagreements with search on 15 625
pairs) nor the carrying criterion (7 479): open (O2).

**C-R3 (an identification drops the leftovers of a merged term).** The same
results and rounds as C-R1 at 2 terms and 6 rounds (386), the identity holds,
and **the ninth's has-a-term criterion agrees with search on every one of
the 15 876 ordered pairs** while the carrying criterion disagrees on 10 284: a
leftover naming a term can be dropped by adding a term and identifying the two,
so the record can always be emptied and the mass is not carried. The choice of
what an identification does to the record decides whether reachability is
one-way.

**C-R1 (chosen)** at the same bound: 386 results, the identity, one-way
reachability by the mass. The three readings agree on the results' ninth
states and differ on the identity (C-R2) and on reachability (C-R3).

## 11. The task's questions

- **Is removing an assertion and admitting its leftover into the same
  relation the identity?** Yes (D1), on the state with its record, and by
  the identity of D1 only: the direct addition instead of the admission
  restores the ninth state and leaves the leftover recorded. Under the set
  reading it is not (§10).
- **Is admitting it into the other relation a genuinely new result?** It is a
  result different from the start and from the direct addition (D2); its
  ninth state is the direct addition's and is a ninth result. New is the
  pairing of that ninth state with a record one leftover lighter — the
  admission is the only change that lightens a record.
- **Does the feedback terminate?** No (D9): a leftover is admitted and
  re-removed without bound, and the record grows without bound (D7). The
  declared bound is C8′; the frontier is exported; the count certifies
  completeness within it (D8).
- **What is the cost of a result?** Its potential, the size plus twice the
  record (D3). An assertion arriving by admission costs three changes, a
  direct addition one, and no shortest sequence from the beginning admits
  (D4).
- **What do reachability, the result set and the count become?** Reachability
  is the carrying of the mass (D5, D6): one-way where the ninth's was mutual.
  The results are every ninth state with any record (D8); the count gains a
  third factor and is again not a product (D8).
- **Which earlier results survive?** §9.

## 12. What does not follow

Each item has two witnesses among the results, or a proof.

- The record is empty — fails: `a; nothing; aℓa` (round 3); holds: every
  result of rounds 0–2 (`nothing_recorded` does not follow).
- A recorded pair is also asserted — fails: `a; nothing; aℓa`; holds: `a; ara;
  aℓa` (`some_recorded_pair_asserted`).
- A change leaves nothing / a pair / a merge / an admissible writing / is an
  admission — each holds of some performed change and fails of another
  (`change_statements_that_do_not_follow`, all six); "is an assertion writing"
  holds of none.
- Any of the ninth's forty-two statements about the asserting, read on the
  ninth state — none holds in every result (9:D14 survives:
  `statements_holding_in_every_result` empty in every run).
- The ninth's add-then-remove returns to the state — refuted (`add_remove_ne`);
  it returns to the ninth state (`add_remove_st`).
- A direct addition changes the record — refuted (`record_not_raised_by_addition`;
  `direct_additions_that_change_the_record` empty).
- The carrying criterion is the two mass invariants — refuted: 4 227 pairs the
  invariants admit and the criterion refuses (§6).
- The count is the ninth's count times the record's — refuted from two terms
  on (§8).

## 13. Open

- O1. Results beyond the declared bounds: the frontier is exported; the
  series gives the count of every round.
- O2. A reachability criterion for the set reading C-R2: neither the ninth's
  nor the carrying criterion agrees with search (§10).
- O3. The sufficiency half of the carrying criterion in Lean (the per-pair
  reshaping path and the identifications following the map); computed only.
  The necessity is in Lean through the mass, not through the map.
- O4. The diagonal mass in Lean (computed: `diagonal_mass_fell` empty).
- O5. A closed form for the number of shortest sequences with two or more
  terms (9:O1 restated); the counts are exact within the bounds
  (`results_with_exact_sequence_count` = results).
- O6. `rename16` (changes commute with rewriting the terms of a state with a
  record): not attempted in Lean; the sameness is implemented and every
  computed check is up to it.

## 14. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Edit distance from the empty two-coloured multigraph.** D3 is an edit
  distance in which a deleted arc is not gone: it becomes a token of its pair,
  a third annotation on the pair beside the two arc colours, weighing two
  (a deletion and an insertion) and convertible into an arc of either colour.
  The ninth's distance (vertices plus arcs) is the special case of an empty
  token set.
- **Conservation in vector addition systems and Petri nets.** D5 is a
  conservation law: the total of arcs and tokens is never lowered by any move,
  and a deletion only moves a unit between an arc and a token. Reachability
  (D6) is then not a token-count test but a carrying condition through a map
  of vertices, since vertices can be merged and never split; that is what
  makes it one-way. The identity of D1 is the reversibility of the
  arc-to-token move, and C-R3 shows the conservation depends on merged
  vertices keeping their tokens.
- **Enumeration of coloured structures (Pólya).** D8 is the cycle index with
  three colour weights per pair, the third doubled; the non-product is the
  ninth's, with a third function.

What appears to be specific to this seed: that the record can enter the state
only as a count per pair that no addition raises and only an admission lowers;
that admission into the same relation is the identity and into the other a
lighter-record twin of the direct addition; that no shortest sequence from
nothing ever admits; that the mass is carried and never lost, which makes
reachability one-way again after the ninth had made it mutual; and that the
one unchosen reading in which a merged term's leftovers vanish restores the
ninth's criterion exactly.
