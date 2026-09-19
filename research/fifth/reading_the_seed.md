# Reading the fifth seed against the fourth and the first

Working notes for the fifth derivation. Nothing here is cited as evidence;
what survived is in `paper/fifth/paper.md` with its source status.

## The diff

`prompt/fifth/seed_prompt.md` against `prompt/fourth/seed_prompt.md`: two
sentences differ.

    - ... it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one.
    + ... it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.

    - A change is exactly one of: adding a term; adding an assertion. Nothing else is a change.
    + A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.

Every other sentence is identical, character for character (`diff`). Against
the first seed (`prompt/seed_prompt.md`) the differences are exactly the
fourth's two multiplicity clauses plus the new removal clause: the fifth seed
is the first seed's four kinds of change on the fourth seed's counted states.

## What the two sentences change

### The state: unchanged

Terms, a multiplicity for each ordered pair, names (`code/fourth/state.py`,
Lean `MSt`). "Asserted" is "multiplicity at least one"; legal is "every `xrx`
at multiplicity zero". Sameness under the two readings, the support and the
indicator, the two beginnings (`arb` once; `bra` once or not at all) — all as
the fourth. Nothing about the state depends on which changes there are.

### Removing an assertion

"Lowers it by one": one change lowers the multiplicity of one `xry` by one.
So removing `xry` asserted `k ≥ 1` times is a change, with outcome `k − 1`;
removing what is not asserted would lower zero, which is no number of times,
so it is not a change (the first derivation's C5, restated for
multiplicities). Removal never makes some `xrx` asserted: never obstructed.

### Identifying two terms

"Replaces both by one term in every assertion." Each `xry` that is asserted
`k` times has its terms replaced in each of the `k` times, so the outcome
asserts `q(x) r q(y)` those `k` times — and when two different assertions
become one, their times add up. Chosen: the multiplicities of the pairs that
become one pair are summed (`fourth.changes.image`, which the fourth already
used to read a build). Unchosen: some other combination, for instance the
larger of the two. Where the two readings differ, the identified pair is
related to a third term both ways; in every proof below identification is
applied only to states with nothing asserted at all, or is used only through
"the merged multiplicity is at least each part" and "the size falls by at
least one", both of which hold under either reading. So the results and the
fewest changes are the same under both readings; only the outcome of an
individual identification differs (a record, not a result). Identifying a
term with itself replaces nothing: not a change (as the first).

Obstruction of an identification: as the first derivation — identifying `u`
and `v` makes some `xrx` asserted exactly when `urv` or `vru` is asserted
(the outcome gives `uru` multiplicity `M(u,v) + M(v,u)`). The obstruction is
those assertions, with their multiplicities. "Remove the obstruction" is now
available: lower `urv` to zero and `vru` to zero (`M(u,v) + M(v,u)`
removals), then identify: a sequence of performed changes. Removing first or
performing the identification and then removing the `uru` that results, as
often as it was made, gives the same state. "Build structure" for an
identification: the state itself (nothing added; the two terms stay two), as
the first.

Obstruction of adding `xrx`: as always. "Remove the obstruction": the
obstruction is the assertion the change itself adds; removing it is not
adding it — refusal (the first derivation's reading; the fourth's
"impossible: no change lowers a multiplicity" no longer applies as a reason,
but the outcome is the same: nothing changes). Builds: the fourth's two
one-term builds (`xrt`, `trx`), through the same criterion with
multiplicities adding up; the criterion is about additions and a map, and
mentions no removal.

### What the fourth derived from "a change only adds" — expected fate

| Fourth's result | Under the fifth seed |
|---|---|
| containment (`Contains4`): a state is contained in its outcome | refuted: removing `arb` from what is given |
| no multiplicity ever decreases; total never decreases | refuted: the same witness |
| the carrying map (second derivation) | refuted: a removal carries `arb` nowhere |
| size rises by exactly one per change | refuted: removal lowers it by one, identification by one (sum reading) |
| every sequence to a result has the same length | refuted: add `bra`, remove `bra` returns to what is given (length 2 and 0) |
| fewest changes = size difference | refuted in general (`a b; nothing asserted` costs 1, size difference −1); survives on results containing what is given |
| results = legal states containing what is given | extends: every legal state with at least one term (the first's D9, with multiplicities) |
| reachability = containment | refuted; the criterion becomes: names one term stay one term (ANCHORED); always (FREE) |
| one-way reachability; a result once left is never returned to; only what is given reaches what is given | refuted: every result with `a ≠ b` reaches what is given; every state reaches itself in two changes |
| fewest classes never decrease | refuted: a removal can lower it |
| `a`, `b` stay two terms; `arb` stays asserted | refuted (ANCHORED): remove `arb`, identify `a`, `b` |
| once `a = b`, always `a = b` (first derivation) | survives (names are carried by the merge map; no change tells them apart) |
| the answers reach nothing new | survives, with the removal answer now a real sequence |
| the two one-term builds | survives (about additions only) |

### The cost: the first derivation's potential, with size counting multiplicities

Let `size = terms + Σ multiplicities` and let `lost` count the destroyed
givens exactly as the first derivation did: with `a ≠ b`, the number of given
assertions (`arb`; and `bra` if given) with multiplicity zero; with `a = b`,
one more than the number of given assertions (2 without `bra`, 3 with).
Then `cost = size + 2·lost` rises by at most one per change:

- add a term: size +1, lost unchanged;
- add `xry`: size +1, a multiplicity rises so lost can only fall;
- remove `xry`: size −1, one multiplicity falls by one, so at most one miss
  appears (`arb` and `bra` are different pairs, and when `a = b` lost is
  constant);
- identify `u`, `v` (unobstructed: nothing between them): terms −1, total
  unchanged (sum reading) so size −1; lost rises by one only when `{u, v} =
  {a, b}` (then nothing was asserted between `a` and `b`, so lost was already
  full minus one) and otherwise the merged multiplicities are at least the
  old ones, so lost cannot rise.

Lower bound: a result reached in `n` changes has `cost ≤ n + cost(given)`
(3 without `bra`, 4 with). Upper bound, target `g` written `a = 0, b = 1`:
remove the given assertions that `g` lacks (lost removals), then `g`
contains the state and the fourth's additions reach it in
`|T_g| − 2 + (total_g − (given total − lost))` changes; total
`size_g − size(given) + 2·lost`. Target with `a = b`: remove the givens,
identify `a` with `b` (the one-term state, `m0 + 1` changes), then additions
(`size_g − 1`): total `size_g + m0 = size_g − (2 + m0) + 2(m0 + 1)`. So
fewest changes = `size − size(given) + 2·lost`, exactly the first
derivation's formula with size counting multiplicities, and the round of a
result is its cost (a result is first met at its fewest changes). Under FREE
the closed form of `lost` is the first's: `m0 + 1` for one term, `m0` for
nothing asserted, `1` with `bra` given and no pair asserted both ways, else `0`.

### Which changes raise the cost by exactly one

Along a shortest sequence every change raises the cost by exactly one. Those
changes are: adding a term; adding an assertion that restores no given;
removing a given assertion (destroying it); identifying `a` with `b`. Every
other change lowers the cost or leaves it. Consequences: a shortest sequence
to a result with `a ≠ b` never has more terms than the result; to a result
with `a = b`, at most one more (everything can be built with `a`, `b` apart
and merged last). So the number of shortest sequences per result, by dynamic
programming over the cost-raising changes within a bound `N` on terms, is
exact for results with fewer than `N` terms or with `a ≠ b`. A shortest
sequence to a result containing what is given uses additions only (no given
is ever destroyed on it, since none is restored), so its shortest sequences
are exactly the fourth's sequences. The sequences of all lengths are
infinitely many for every result: add `xry`, remove `xry` (two terms) or add
a term, identify it back (one term) returns to the state.

### Reachability

From any state with `a ≠ b` (ANCHORED): remove everything, identify every
other term into `a`, move the names to fresh terms and then to the target's
named terms (identify `new` with `old`: the surviving term is the first), add
the missing terms and raise the multiplicities: any legal state with names
anywhere is reached. From a state with `a = b`: only states with `a = b`
(names stay merged). So: `s` reaches `t` exactly when `s.a = s.b → t.a =
t.b`. Under FREE (no names): always. Reachability is mutual within the two
classes; between them one-way (apart → merged). Every result with `a ≠ b`
reaches what is given. Containment still implies reachability (additions).

### Counting

Every legal state with at least one term is a result, so the independent
count is the first derivation's (all legal states by terms and how the named
terms stand: one term / neither / `arb` only / `bra` only / both) computed
with the fourth's series per pair cycle instead of the binomial, by terms and
total multiplicity. Completeness within a bound on terms `N` and rounds `R`:
a legal state with `≤ N` terms and cost `≤ R` is on a shortest sequence whose
states have at most `max(2, terms)` terms (the upper-bound path) and cost
equal to their position, so it is found in round = cost. The certificate
compares explored results by (terms, total, lost-kind) with the count
restricted to cost `≤ R`.

With two terms all 100 rounds complete: round `r` has about `2r` results
(names kept, no `bra`): `r + 1` with `arb` and both names apart, one with
`arb` missing, and `r − 2` with `a = b` and a second term.

### Attempts per result

`C(n, 2)` identifications, one removal per asserted pair (`d` of them), one
term, `n²` additions: `C(n, 2) + d + 1 + n²`; obstructed: the `n` additions of
`xrx` and the identifications of related pairs. The frontier: adding a term
on an `N`-term result and the two builds of each of its `N` obstructed
additions, `1 + 2N` entries as before (an identification's answers never
leave the bound).

## What must be checked per citation (rule 5)

| Earlier result | Expected under the fifth seed |
|---|---|
| 1:D1 `a ≠ b` in a legal state asserting `arb` | survives (no change involved) |
| 1:D3 which changes are obstructed | survives with multiplicities (re-proved on `MSt`) |
| 1:D4 adding `xrx` always obstructed | survives |
| 1:D5 what clears an obstruction: only removal | survives, `M(u,v) + M(v,u)` removals |
| 1:D6 every result legal, ≥ 1 term, finite | survives |
| 1:D7 `a = b` irreversible; `arb` gone for good | survives |
| 1:D8 cost = size difference + 2·lost | survives with size counting multiplicities (re-proved) |
| 1:D9 every legal state is a result | survives with multiplicities |
| 1:D10 answers reach nothing new | survives; the removal answer has `M(u,v) + M(v,u) + 1` changes |
| 1:D11 one-term builds `3 · 2^d` | does not survive (the fourth's two, 4:D10) |
| 4:D5–D7 containment, persistence, no decrease | do not survive (witnesses) |
| 4:D8 size rises by one; same length; cost = size difference | do not survive; cost survives on results containing the given |
| 4:D9 results = states containing the given | does not survive as stated; those are the results of cost with lost = 0, at the same rounds |
| 4:D12 reachability = containment | does not survive; containment still sufficient |
| 4:D13 one-way; split never decreases | do not survive |
| 4:D3 obstruction of additions; `1 + n²` | additions part survives; the count gains identifications and removals |
| 4:D10 answers; two one-term builds | survives |
| 4:D14 completeness by series | survives with the lost-kind split |
| 4:D17 two-term closed forms | partly: the `(1 + i, j)` results and their `C(i + j, i)` shortest sequences survive; more results per round now |
| 4:K counts | the fourth's numbers are the lost = 0 part; computed again as such |
| 2:D12 carrying-map reachability | does not survive (removal) |
