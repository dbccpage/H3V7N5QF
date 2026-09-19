# Reading the sixth seed against the fifth

Working notes for the sixth derivation. Nothing here is cited as evidence;
what survived is in `paper/sixth/paper.md` with its source status.

## The diff

`prompt/sixth/seed_prompt.md` against `prompt/fifth/seed_prompt.md`: two
passages are gone, nothing is added.

    - - For no term `x` may `xrx` be asserted.

    - A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing.

Every other sentence is identical, character for character (`diff`). So the
sixth seed is the fifth seed's counted states and four kinds of change with
nothing forbidden: `xrx` is an assertion like any other, with a multiplicity
like any other; no attempt is obstructed; nothing is answered, refused or
built. "Attempt every change" now means "perform every change".

## What the removal of the two passages changes

### The state: the same structure, more states

Terms, a multiplicity for each ordered pair, names (`code/fourth/state.py`,
Lean `MSt`) — the diagonal pairs `(x, x)` were always in the model (a
`MState` "may hold some `xrx`; then it is not legal"), so the model needs no
change; what changes is that these states are now results. "Legal" stops
being a condition and becomes a property a state may or may not have ("no
`xrx` asserted"), tested like any other statement. Sameness, the support and
the indicator, the two beginnings (`arb` once; `bra` once or not at all) are
as the fifth. The one-term state can now assert `ara`, any number of times.

### The changes: the same four kinds, none obstructed

Adding `xrx` raises its multiplicity like any addition. Identifying `u` and
`v` replaces both by one term in every assertion; with the sum reading
(C5″), the four pairs `urv`, `vru`, `uru`, `vrv` all become `uru`, whose
multiplicity is the sum of theirs. Removing `xrx` lowers it by one. So a
result with `n` terms and `d` asserted pairs (diagonal pairs included) has
`C(n, 2) + d + 1 + n²` changes, every one performed. The fifth's obstructed
attempts — the `n` additions of some `xrx` and the identifications of related
pairs — are the attempts whose outcome asserts some `xrx` while the state
does not; that is still a fact about the outcome (Lean `Step6.legal_iff`), no
longer a bar. On a state that already asserts some `xrx`, nearly every
change keeps it.

### The answers: gone; what the fifth recorded as an answer is now just a sequence

Refusal: nothing to refuse. "Remove the obstruction" for an identification of
`u`, `v` (lower `urv`, `vru` to zero, then identify) is still a sequence of
changes, and so is the direct identification; they reach different states —
`uru` at multiplicity zero versus `M(u,v) + M(v,u) + M(u,u) + M(v,v)` — both
results. The fifth's `remove_obstruction_first_or_last5` (removing first, or
identifying and then lowering the resulting `uru` to zero, give the same
state) used legality: with `uru` or `vrv` asserted before the identification
the second path also destroys those, so the statement does not survive as
stated; it survives on states with nothing at `uru`, `vrv`. Builds: the two
one-term builds are two additions and their outcomes are results, like every
state; they answer nothing.

### The cost: the fifth's potential fails, and why

The fifth's potential is `size + 2·lost` with `lost = m0 + 1` when the names
are one term. Identifying `a` and `b` in what is given is now one change
(outcome `a (a and b one term); ara`, size 2), while the fifth's `lost`
jumps from 0 to `m0 + 1`, raising its potential by `2m0 + 1` (three without
`bra`): the identification case of `Step5.costA_le` used that nothing was
asserted between the merged terms, which is exactly what is no longer
required.

The repair: when the names are one term `c`, count the destroyed givens as
`m0 + 1 − min(M(c,c), m0)`. Reason: the given assertions, after the merge,
are `crc`; a merge that carries `k` of them keeps `k`; the extra `+1` is the
merge itself. With the names apart, `lost` is as before (the givens with
multiplicity zero). Then `Φ = size + 2·lost` rises by at most one per change:

- add a term: size +1, lost unchanged;
- add `xry` (`x = y` allowed): size +1, a multiplicity rises so lost can only
  fall (names apart: a given may be restored; names one term: `crc` may rise);
- remove `xry`: size −1, one multiplicity falls by one, so lost rises by at
  most one (names apart: `arb`, `bra` are different pairs; names one term:
  `min(M(c,c), m0)` falls by at most one);
- identify `u`, `v` (always allowed): size −1 (total kept, sum reading);
  names apart before and after: the merged multiplicities are at least the
  old ones, lost cannot rise; names merged before: `M'(c,c) ≥ M(c,c)`, lost
  cannot rise; `{u, v} = {a, b}`: before, `lost = m0 − p` with `p` the number
  of present givens; after, `M'(c,c) = M(a,b) + M(b,a) + M(a,a) + M(b,b) ≥ p`,
  so `lost' = m0 + 1 − min(M'(c,c), m0) ≤ m0 + 1 − p = lost + 1`.

Lower bound: a result reached in `n` changes has `Φ ≤ n + Φ(given)`, and
`Φ(given) = 2 + m0`. Upper bound, target `g` written `a = 0`:

- `b = 1` (names apart): remove the given assertions `g` lacks (`lost`
  removals); `g` contains the state reached; additions reach it (the fourth's
  path, re-proved without legality: `xrx` is added like any pair);
- `b = 0` (names one term): let `k = min(M_g(0,0), m0)`; remove `m0 − k` of
  the givens (1 change each), identify `0` and `1` (the one-term state with
  `0r0` asserted `k` times), then add the rest: `(m0 − k) + 1 + size(g) − 1
  − k = size(g) + m0 − 2k = size(g) − (2 + m0) + 2·(m0 + 1 − k)`.

So the fewest changes is `size − size(given) + 2·lost` with the new `lost`,
and the round of a result is its cost. The formula agrees with the fifth's
on every state with no `xrx` (there `M(c,c) = 0`) and on every state with the
names apart; it differs exactly on the states with the names one term and
`crc` asserted. The fourth's size difference survives on states containing
what is given, as before.

Under FREE the names may be placed at will: `lost_free = min(apart, merged)`
with `apart` (two or more terms) the fifth's closed form — `m0 = 1`: 0 if
some `xry` with `x ≠ y` is asserted, else 1; `m0 = 2`: 0 if some pair is
asserted both ways, 1 if some `xry`, `x ≠ y`, else 2 — and `merged = m0 + 1 −
min(max_c M(c,c), m0)`. Checked by placement in `scratch_check.py` (not
evidence) on every state with at most three terms and no multiplicity above
two: no mismatch. Example: `c d; crc crc` with `bra` given costs 2 (identify,
add a term), not the fifth's 4.

### Which changes raise the cost by exactly one

Along a shortest sequence every change raises `Φ` by exactly one. These are:
adding a term; adding an assertion unless it restores a given (names apart)
or is `crc` with `M(c,c) < m0` (names one term); removing a given asserted
once (names apart) or `crc` with `M(c,c) ≤ m0` (names one term); identifying
`a` with `b` when `min(S, m0) = p` where `S = M(a,b) + M(b,a) + M(a,a) +
M(b,b)` and `p` is the number of present givens. Every other change lowers
the cost. Consequences for the shortest-sequence counts: to a result with
the names apart, no identification occurs, so the sequence never has more
terms than the result — exact within any bound holding the result; to a
result with the names one term, at most one more term (as the fifth); under
FREE, exact when the result has fewer terms than the bound or no optimal
placement puts the names on one term (if one does, a shortest sequence may
add a term before the merge and pass through one more term than the result:
`c d; crc` with `m0 = 1` has `apart = merged = 1`, and "add a term, identify"
is a shortest sequence through three terms).

### What the fifth derived from legality — expected fate

| Fifth's result | Under the sixth seed |
|---|---|
| which attempts are obstructed (D3) | no attempt is obstructed; the characterisation survives as "which changes make some `xrx` asserted" |
| answers: refuse / remove / build (D5, D10) | gone; the removal answer and the direct identification are two sequences to two different results |
| `remove_obstruction_first_or_last5` | fails as stated (witness: `uru` asserted before); survives with nothing at `uru`, `vrv` |
| every result is legal (D6) | fails: `a b; arb ara` is a result (one change) |
| `arb` never asserted again once `a = b` (D7, `arb_gone_for_good`) | fails: after the merge `arb` is `ara`, asserted after identifying what is given |
| names once one term stay one term (D7) | survives (mentions no legality) |
| cost = size − size(given) + 2·lost (D8) | survives on states with the names apart and on states with no `xrx`; the destroyed givens of a state with the names one term change |
| every change moves the cost by an odd amount; parity (D8(v)) | survives (size moves by one; lost enters twice) |
| the results are every legal state with ≥ 1 term (D9) | extends: every well-formed state with ≥ 1 term; the fifth's are exactly those with no `xrx`, at the same rounds |
| reachability = the names (D12) | survives, re-proved without legality; containment still sufficient |
| mutual within classes, comparable, two-change cycle (D13) | survives |
| shortest-sequence counts (K7) | the fifth's on its results with the names apart (FREE: two or more terms); larger on the others (identify first, then remove `ara`) |
| `C(n, 2) + d + 1 + n²` changes, `n + related` obstructed (D3) | the count survives with `d` counting diagonal pairs; none obstructed; `n + related` make some `xrx` asserted on a state with none |
| two one-term builds (D10) | two additions, answering nothing |
| two-term closed forms (D17) | more results per round: `C(r+3, 3) + C(r+1, 2) + C(r+1, 3) + C(r−1, 2) + one(r)` without `bra` (see below) |
| the independent count by legal states (D14) | the diagonal pairs join the cycles; the legal part is the fifth's count |

### Reachability

From any well-formed state with `a ≠ b`: remove everything, identify every
other term into `a` (always allowed now), move the names by fresh terms, add
what the target has — `xrx` included. From a state with `a = b`: only states
with `a = b`. So `s` reaches `t` exactly when `s.a = s.b → t.a = t.b`, as
the fifth, for *every* well-formed `t` with a term; FREE: always. The fifth's
proof (`reach5_of_names`) had `g.Legal` among its hypotheses only to feed
`reach4_of_contains`; with an addition path that adds `xrx` like any pair
the hypothesis goes.

### Counting

All well-formed states with `n` terms up to rewriting, by total
multiplicity: the fourth's series `1 / (1 − x^L)` over the cycles of the
rewriting's action on *all* `n²` ordered pairs — the `n² − n` off-diagonal
cycles of the earlier derivations plus, for each cycle of the rewriting of
length `p`, one cycle of length `p` of diagonal pairs. With names: the fifth's
five kinds, the "one term" kind split by how often `crc` is asserted at the
named term (0, 1, 2 or more), since `lost` depends on `min(M(c,c), m0)`. Under
FREE, `lost_free` needs the joint distribution of "some off-diagonal
asserted / some pair both ways" and "largest diagonal multiplicity": counted
by series with the diagonal factor capped (`1 + x^L + … + x^{(m−1)L}` for
"every diagonal below `m`") and the off-diagonal factor 1 for "nothing
off-diagonal". Restricting the diagonal to zero gives the fifth's counts — the
computed form of the citation.

### Two terms, all rounds

With the given terms only (names kept, `bra` not given), the results of
round `r`: names apart, `arb` `1 + i` times, `bra` `j`, `ara` `p`, `brb` `q`
with `i + j + p + q = r`: `C(r+3, 3)`; `arb` missing, `j + p + q = r − 1`:
`C(r+1, 2)`; the one-term state with `ara` `K` times, cost `2` for `K = 0`
and `K` otherwise: one result in every round `r ≥ 1`, two in round 2; the
names one term with a second term, `crc` `K` times: `K = 0`: `C(r−1, 2)`
(`r ≥ 3`), `K ≥ 1`: `C(r+1, 3)` (`r ≥ 2`). Total 1, 6, 16, 32, 59, 98, 151,
220, …: cubic growth, so the seed's 100 rounds (about four million results)
do not complete in minutes; a bound on rounds is declared and the closed form
proved for every round. With `bra` given: `C(r+3, 3) + 2·C(r+1, 2) + (r − 1)
[r ≥ 2] + one_b(r) + C(r−2, 2)[r ≥ 4] + C(r−1, 2)[r ≥ 3] + C(r+1, 3)[r ≥ 2]`
with `one_b = 0, 1, 2, 2, 1, 1, …`: 1, 7, 20, 41, 73, 120, 183, 264, ….
Shortest sequences to a two-term result with the names apart: the
arrangements of its cost-raising changes — `i` (or `i − 1`) additions of
`arb`, or its one removal; likewise `bra`; `p` of `ara`, `q` of `brb` —
a multinomial coefficient.

## What must be checked per citation (rule 5)

| Earlier result | Expected under the sixth seed |
|---|---|
| 4:D1, 1:D1 `a ≠ b` in a legal state asserting `arb` | survives on legal states only; in general `a = b` with `arb` (= `ara`) asserted is a result |
| 5:D2 the beginnings reach each other | survives (embedding) |
| 5:D3 obstructed attempts | the characterisation survives as `Step6.legal_iff`; "obstructed" is empty |
| 5:D4 adding `xrx` always obstructed | fails: it is performed |
| 5:D5 persistence, the removal answer | the removal sequence survives as a sequence; its outcome differs from the identification's |
| 5:D6 every result legal, ≥ 1 term, finite | legality fails; the rest survives |
| 5:D7 names stay merged; `arb` gone for good | the first survives; the second fails |
| 5:D8 cost | survives on names apart and on legal states; changes on names one term with `crc` |
| 5:D9 everything legal is a result | extends to everything well formed |
| 5:D10 answers reach nothing new | vacuous (no answers) |
| 5:D11 rename | survives (`rename4_remove`, `rename4_identify` mention no legality) |
| 5:D12 the names criterion | survives, re-proved |
| 5:D13 mutual, comparable, cycles | survives (embedding) |
| 5:D14 completeness by counts | survives with the diagonal cycles |
| 5:D17 two-term closed forms | replaced by the cubic forms; the fifth's results are a part |
| 5:K1–K8 | computed again; the legal part must match |
| 4:D12 containment sufficient | survives (additions are changes) |
| 4:reach4_of_contains | needs `g.Legal`; re-proved as `reach6_of_contains` without it |
