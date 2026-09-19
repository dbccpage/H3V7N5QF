# Reading the seventh seed against the sixth

Working notes for the seventh derivation. Nothing here is cited as evidence;
what survived is in `paper/seventh/paper.md` with its source status.

## The diff

`prompt/seventh/seed_prompt.md` against `prompt/sixth/seed_prompt.md`: one
passage is replaced.

    < Given:
    <
    < - `arb` is asserted with multiplicity one.
    <
    < Whether `bra` is asserted is not given.
    ---
    > Nothing is given: to begin with there are no terms and nothing is asserted.

Every other sentence is identical, character for character (`diff`). So the
seventh seed is the sixth seed's counted states and four kinds of change,
nothing forbidden, from an empty beginning: no terms, nothing asserted, no
`a`, no `b`.

## What the replacement changes

### The state: the sixth's without names

Terms, a multiplicity for each ordered pair (`code/fourth/state.py`
`MState`, with `names = None`) — the model needs no change; the names were
optional there already (the FREE reading never carried them). What changes:
a state may have *no* terms (`MState(0, ())`, always representable: the
first derivation allowed `n = 0` in the model and refuted it as a result;
now it is the beginning). Lean: the sixth's `MSt` has the names as fields and
`WF` puts them among the terms, so a state without terms is not well formed
there; a new structure `NSt` without names is needed, with two maps:
`forget : MSt → NSt` (drop the names) and `name : NSt → ℕ → MSt` (put both
names on one term `c`; well formed exactly when `c` is a term).

### Sameness: one reading

"Two results that differ only in how their terms are written are the same
result." The earlier derivations read this two ways: any rewriting (FREE)
and rewritings keeping `a`, `b` (ANCHORED). With no `a` and no `b` the second
reading has nothing to keep: every rewriting keeps the names, and the two
readings coincide. Not a choice any more — derived from the absence of names.
So one beginning (the empty state; no `bra` alternative) and one reading:
one exploration per bound instead of the sixth's four.

### The changes: the same four kinds

Identify two terms (needs two terms), remove an assertion (needs one
asserted), add a term, add an assertion (needs terms). On the empty state the
list of changes is "add a term" alone (`fifth.changes.changes` gives exactly
that on `n = 0`). So the first change is forced: the task says so, and it is
a theorem (`first_change_adds_term`). A result with `n` terms and `d`
asserted pairs has `C(n, 2) + d + 1 + n²` changes, as the sixth.

### The one irreversible change: leaving the empty state

Every change on a state with a term leaves a state with a term (a term is
added; an assertion is between terms; a removal keeps the terms; an
identification of two terms keeps one). And the only change on the empty
state adds a term. So once a state has a term every later state has a term,
and the empty state is reached from a well-formed state only from itself, in
zero changes. This replaces the sixth's one-way merge of the names (which
has no referent now): the seventh's "one-way property" is *having a term*.

### The cost: the size, nothing destroyed

Nothing is given, so nothing can be destroyed: the sixth's `lost` has no
object. The size (terms plus the sum of the multiplicities) moves by exactly
one per change (+1 for the two additions, −1 for removal and identification —
the sixth's `Step6.size_step`, which mentions no names), so from the empty
state (size 0) a result of size `k` needs at least `k` changes; and `k`
additions reach it (the terms, then the assertions). So

    fewest changes to a result = its size,

the round of a result is its size, and every shortest sequence is additions
only (a removal or identification in a sequence of length = size would leave
the size below the length). Compared with the sixth: the sixth's FREE cost
from `arb` is `size − 3 + 2·lost_free` (no `bra`); the one-term state
asserting nothing costs 2 there and 1 here; the two-term state asserting
`arb` once (the sixth's beginning) costs 0 there and 3 here. The fourth's
"size difference" survives with `size(given) = 0`.

Parity: the size and the length of a sequence have the same parity
(`Reach7.size_parity`); no change keeps the round.

### The results: every well-formed state, the empty one included

From the empty state additions reach every well-formed state; so the results
are all of them. The sixth's results (FREE) are the well-formed states with
at least one term; with the names forgotten, the sixth's ANCHORED results are
the same set. The seventh has one result no earlier seed has: the empty
state, round 0 (`Reach6.nonempty`: no sixth sequence ends without a term).

### Reachability: a term decides

From a well-formed state with a term every well-formed state with a term is
reached: the sixth's path (remove everything, identify every other term into
one, add what the target has) through `name` — put both names on a term `c`
of the start, on a term `c'` of the target; `reach6_of_names` needs
`s.a = s.b → g.a = g.b`, which holds trivially. From the empty state every
well-formed state is reached (additions). No state with a term reaches the
empty state. So

    t is reachable from s  ⟺  t has a term, or s is empty  ⟺  (s has a term → t has a term).

Mutual among the states with a term; one-way out of the empty state; any two
results comparable; every state with a term has the two-change cycle (add
`xry`, remove it; or add a term, identify it back) — the empty state has
none, and it is the only result with no cycle.

### What does not follow

Every well-formed state is a result, the empty one included, so no statement
about the asserting that fails in some well-formed state holds in every
result: the sixth's "at least one term" now fails at round 0. Of the
statements tested (the sixth's sixteen unnamed ones plus "no terms and
nothing asserted"), every one holds in some result and fails in another.
Nothing about the asserting is forced from nothing. What *is* forced: the
first change (a term), the cost of every result (its size), the one-way exit
from the empty state, the number of changes of a result.

### Counting

All well-formed states with `n` terms up to rewriting, by total multiplicity
`t`: the sixth's `count_free(n, ·)` (the diagonal pairs among the cycles),
with `n = 0` giving the empty state alone. Results of round `r` without
bound: `Σ_{n ≤ r} count_free(n)[r − n]`. With at most two terms:
`n = 0`: one result in round 0; `n = 1`: `ara` `r − 1` times, one result in
every round `r ≥ 1`; `n = 2`: the four multiplicities `(p, i, j, q)` of
`ara`, `arb`, `bra`, `brb` summing to `t = r − 2`, up to the swap
`(p, i, j, q) ↔ (q, j, i, p)`: `(C(t+3, 3) + [t even](t/2 + 1)) / 2`. So the
results of round `r`: 1, 1, 2, 3, 7, 11, 20, 29, 45, 61, 86, … — cubic
growth; 100 rounds hold about two million results with two terms alone.

### Shortest sequences

Additions only; counted change by change on the least writings (the
protocol of the earlier derivations). One-term results: exactly one
sequence (add a term, then `ara` `k` times). Two-term results: no closed form
attempted (the least-writing identification of `arb` with `bra` makes the
count differ from a multinomial); computed per result, exact within any
bound holding the result (a shortest sequence never has more terms than its
target).

## What must be checked per citation (rule 5)

| Earlier result | Expected under the seventh seed |
|---|---|
| the counted state, sameness (4:C1′, 4:C4) | survives with `names = None`; the two readings coincide |
| `remove`, `identify`, the change record, the list of changes, `perform` (5:C5″, 6:C5‴) | survive (they mention no name and no given); on the empty state the list is one change |
| `Step6.size_step`, `Reach6.size_parity` (6:D8(v)) | survive through `name` on states with a term; the empty state's only change raises the size |
| `reach6_by_additions`, `reach6_of_contains` (6:D8(ii)) | survive through `name` once a term is there; from the empty state the first term is added first |
| `reach6_of_names`, `reach6_iff` (6:D12) | the criterion loses its object; through `name` it says "always" on states with a term; the seventh adds the empty-state clause |
| `Step6.names_stay_merged`, `Reach6.names_stay_merged` (6:D7) | trivial through `name` (`c = c`); replaced by "a term stays" |
| `costA6`, `costB6`, `fewest_changes6_*` (6:D8) | do not survive (no given to measure from); witness: the one-term state |
| `fewest_changes6_of_contains_*` (4:D8, 6:D8) | survives as "the size difference" with `size(given) = 0` |
| `cycle2_6`, `Reach6.unbounded` (6:D13) | survive through `name` on states with a term; the empty state has no cycle |
| `count_free` with the diagonal pairs (6:D14) | survives (no names); `n = 0` added |
| the statements tested (4:N3, 5:N3, 6:N3) | the unnamed ones survive as statements; "at least one term" is no longer everywhere true |
| 6:K1–K8 | computed again: the sixth's FREE results are the results with a term, at the rounds the sixth's cost formula gives; its ANCHORED results with the names forgotten are the same set |
| `two_states_on_given_terms`, `bra_not_derived`, `bra_not_refuted` (1:D2, 1:N1, 1:N2) | without object (no given, no `bra`) |
