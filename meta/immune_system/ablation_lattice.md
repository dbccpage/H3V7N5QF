# Seed-edit matrix (outside the derivational seal)

**Chosen:** a seed sentence is one row; each cell describes the literal edit
from that derivation's named parent, not an inferred causal effect. `K` = kept
byte-for-byte, `R` = replaced, `D` = dropped, `A` = added. `S` marks the base
source, which has no parent. The exact diffs are in
`meta/review/reading_index.md`; this matrix groups a multi-line beginning as
one sentence block. Derivations 10–15 and 17–21 branch, so reading this as a
single chain would be wrong.

| Sentence block | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Terms, assertion notation and multiplicity | S | K | K | R | R | K | K | R | K | K | K | K | K | K | K | K | K | K | K | K | K |
| Beginning: given `arb` or nothing | S | K | K | R | K | K | R | R | R | K | K | K | K | K | K | K | K | K | K | K | K |
| Ban on `xrx` | S | K | K | K | K | D | K | K | K | K | K | K | K | K | K | K | D | K | K | K | K |
| `bra` and other assertions unspecified | S | K | K | K | K | K | D | A | D | K | K | K | K | K | K | K | K | K | K | K | K |
| Four kinds and identifying sentence | S | R | R | K | R | K | K | K | K | K | K | R | K | K | K | K | K | K | R | K | K |
| Obstruction and answer paragraph | S | K | K | K | K | D | K | K | K | K | K | K | K | K | K | K | K | K | K | K | R |
| Extra sentence on a record, writing or admission | S | K | K | K | K | K | K | K | K | A | A | K | A | A | A | R | K | K | K | K | K |
| Attempt priority and sameness of results | S | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | R | K | R | K |
| 100 changes, bounded frontier protocol | S | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K |
| Question and output paragraphs | S | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K | K |

Parent edges are `1→2→3→4→5→6→7→8→9`, except the eighth also restores a
beginning while adding `s`; `9→10,…,15`; `14→16`; and `1→17,…,21`. Each
branch's `K` is relative to its own parent. The record inserted in 12 is in
the identifying sentence, so its R appears on that row rather than the
extra-sentence row. The labels are **computed** from the local seed diffs,
then checked against the literal changed lines.

## Do edits commute?

**Derived on the final seed text, computed on finite maps:** “empty
beginning” and “add relation `s`” both occur in the ninth. Applying them to
the sixth seed in either order yields the ninth's empty, two-relation seed;
the eighth is the named intermediate with `s`, the seventh the empty
one-relation intermediate. The exact ninth state type/cost is the same at
the endpoint. The object square 6→8→9 versus 6→7→9 agrees on all 66 named
binary states with one or two terms in `map_checks.json`. The ninth's
`seventh_derivation` comparison checks the one-relation parts and its
`eighth_derivation` comparison checks forgetting names on its declared
bounds (`evidence/ninth/summary.json`). The intermediate *cost functions*
are different: the ninth summary counts thousands of shared states where
the eighth's cost is below the ninth's. Thus the commuting endpoint does not
make each edge cost-preserving.

**Open:** the repository does not contain both orders for most pairs of
edits, so there is no commutation finding to inherit. Concrete tests:

| Pair | Missing joint seed and falsifier | Status |
|---|---|---|
| Strike the ban (17) then make identification partial (19), and reverse | A joint one-assertion rewrite on a state already asserting `xrx` could be admitted in one order and refused in the other; compare both response readings within 3 terms | open |
| Distinguish written forms (18) then require refusal (21), and reverse | Compare the written closure and orbit quotient at 3 terms under equal rounds; a writing present on only one route refutes commutation | open |
| Admit a leftover (16) then require refusal (21), and reverse | First decide which changes can write `xrx` and whether admission is such a change; compare the record and refusal log on the same two-term state | open |
| Count assertions (4) then remove the `xrx` ban (6), and reverse | The sixth is the counted-ban-removed endpoint; a Boolean ban-removed intermediate is not an existing derivation. Compare support/indicator paths, including re-adding a loop | open |

For each open row, both orderings are legal candidate readings. Neither is
discarded as isomorphic without a map and a result/cost comparison. The
matrix records variation present in the repository; it does not prove a
general algebra of seed edits.
