# Change log, twenty-fourth derivation

Each material change, and its reason. Newest last. Commits are on the branch
`derivation/twentyfourth`; nothing is pushed.

1. **`CLAUDE.md` gained the twenty-fourth derivation's plan and stopping
   conditions (AM1–AM10), committed alone before any other work.** Reason:
   required by `prompt/twentyfourth/prompt.md`. Words of the plan were probed
   against the prose watchlist (`--probe`) before it was written, and the
   watchlist was run before the commit.

2. **Layout: a new package `code/twentyfourth/`, launchers
   `code/run_twentyfourth.py` and `code/lean_report_twentyfourth.py`; no earlier
   module is modified.** Imported: the twenty-third's state helpers
   (`excess_table`, `normal_table`, `nothing_certificate`, `plain`), its cost by
   raising sets (`cost`, `record`, `fewest_states`), its grouped exploration and
   shortest-sequence counts (for the comparison), its statements and its orbit
   helpers; the ninth's changes and `perform`; `xry.changes.identification_map`,
   `fourth.state._rewritings`; the writers, `compare_evidence` and the Lean
   report helpers. Defined afresh: the state with filled terms, its least
   writing and the mark of its result, the five changes under each reading, the
   exploration and grouping, the cost, the balance record and the classes of
   D5, the independent counts, the maps in and back, reachability, the readings,
   the statements, and `FillCheck` with seventeen disagreement lists.

3. **Bounds.** The plan's targets were kept: 5 terms and 7 rounds, 3 and 9, 2
   and 16. Five terms at eight rounds was tried (research
   `try_counts.py`): it completed, but its independent listing count took over
   a minute, so the planned seven rounds were kept for the regenerated
   evidence.

4. **`Plan` checks two preconditions of the searches** (the sameness joins
   within three times the states' assertions; reachability needs two terms and
   three rounds). Reason: a very small plan in the launcher test first made
   the reachability search miss the C-I2 unfilling detour (through a second
   term at cost three) and the sameness search miss joins; the checks now say
   so instead of reporting a disagreement.

5. **Lean: `lean4_core/Twentyfourth/`** (142 theorems in nine files). The
   lakefile gained the library and a default target, appended without touching
   what was there (recorded in `paper/twentysecond/change_log.md`, item 15,
   since the lakefile is the twenty-second's). Two proofs first depended on
   `Classical.choice`, which the report refuses: a term-mode pattern lambda
   followed by `subst` in the base case of `reach24_collapse` (rewritten in
   tactic form), and `by_cases` on `FSt.HasFilled`, a definition for which no
   decision was found, so the tactic fell back on a classical one (an explicit
   instance deciding it by searching the terms was added). The probes are kept
   in `research/twentyfourth/probe_choice.lean` and `probe_decidable.lean`.
   Target 7 (every writing) closed: `SameW24`, `SameW24.balances`,
   `SameW24.told`, `cost24_every_writing`.

6. **The axiom report also prints the sixteen earlier theorems the paper and
   ledger name** (a section at the end of `Twentyfourth/Axioms.lean`, written by
   `research/twentyfourth/make_axioms_file.py`). Reason:
   `ci/check_axiom_citations.py` requires every cited Lean name in this
   derivation's own report; the earlier theorems are imported and re-checked
   by Lean when this library is built.

7. **Shared files, only added to:** `ci/check_mutation_bite.py` gained the
   twenty-fourth panel (seventeen fields, each biting under its mutation) and
   its entry in `panels()`; `ci/check_axiom_citations.py` lists
   `twentyfourth`; `ci/check_definitional_citations.py` gained the record noun
   `fill` for this derivation, so that a ledger row about filled terms cannot
   rest on a reflexivity theorem that does not name them.

8. **Every earlier derivation's evidence was re-checked with its `--check`
   after this derivation's code was in place**
   (`research/twentyfourth/check_earlier.py`); the outcome is recorded in the
   commit message.
