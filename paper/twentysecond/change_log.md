# Change log, twenty-second derivation

Each material change, and its reason. Newest last. Commits are on the branch
`derivation/twentysecond`; nothing is pushed.

1. **`CLAUDE.md` gained the twenty-second derivation's plan and stopping
   conditions (AK1–AK10), committed alone before any other work.** Reason:
   required by `prompt/twentysecond/prompt.md`. The earlier plans above it are
   unchanged.

2. **Lean: a new Lake package `lean4_core/` (toolchain
   `leanprover/lean4:v4.33.1`, no `require`), library `Twentysecond`.** Reason:
   the task requires a package that does not import the libraries in `lean4/`.
   The ninth's state is re-written without the outside library — terms
   `0 … n − 1`, assertions as a list of atoms counted — and identification
   writes the last term in the freed place (a rewriting of the ninth's outcome).
   The seventh's state likewise (`St7`). Everything used is re-proved there.
   `lean4_core/lake-manifest.json` (no packages) is committed; `.lake/` is not.

3. **Lean: the core library's `List.erase`, `List.perm_iff_count`,
   `List.perm_cons_erase` and `List.Perm.erase` depend on `Classical.choice`
   (probed with `#print axioms`), so one-occurrence deletion is defined afresh
   (`del`) with its lemmas, and "same counts ⇒ rearrangement" is re-proved
   (`perm_of_count`).** Reason: the task allows only `propext` and `Quot.sound`.
   Three proofs first closed through lemmas or tactics that bring in choice
   (`simp` on a list length; `omega` closing a goal that is not arithmetic, which
   argues by contradiction classically); each was rewritten by case analysis,
   and the report now lists every theorem within the two allowed axioms.

4. **Lean target 7 (rewriting and the full sameness) closed on the single
   attempt** (`genW_iff_sameW`, `ofR_sameW_iff`,
   `fewest_changes_every_writing`, `plain_states_stay_apart_every_writing`).
   Theorems added after the first draft of the paper, to back its claims:
   `Step.phi_parity`, `Step.not_same`, `shortest_all_plain`,
   `same_ofR_of_readBack`, `first_change_adds_term`, `phi_ofR`.

5. **Layout: a new package `code/twentysecond/`, launchers
   `code/run_twentysecond.py` and `code/lean_report_twentysecond.py`; no earlier
   module is modified.** Imported: the ninth's state, `canonical`, `swap`,
   `rewrite`, `of_r`, the change record, `changes`, `perform`, `is_addition`,
   the ninth's and seventh's explorations and sequence counts for the
   comparisons, `ninth.follows.STATEMENTS`, `xry.orbits.partitions` and
   `class_size`, `xry.changes.identification_map`, the writers,
   `compare_evidence`, the Lean report runner. Defined afresh: the excess, the
   plain state, the result, the record and the rule of how each change moves
   it, the exploration of results, the count by cycles and the closed forms,
   reachability, the seventh embedding and the map back, the unchosen readings,
   the checks (`JointCheck`, sixteen disagreement lists).

6. **`ci/check_mutation_bite.py` gained a twenty-second panel (sixteen bite
   cases, one per field of `JointCheck`).** Reason: required by the task; each
   case perturbs one function in `twentysecond.evidence`'s namespace and the
   field it guards fires.

7. **`ci/check_axiom_citations.py` and `ci/check_definitional_citations.py`
   read `lean4_core/` besides `lean4/`, and the first lists the twenty-second
   derivation.** Reason: both read `lean4/` only, so this derivation's
   citations of `lean4_core/` theorems would have been skipped rather than
   checked. No earlier derivation's result changes: the earlier ledgers cite
   `lean4/` names, resolved first in their own library as before.

8. **Bounds.** The plan's targets completed in minutes and are the bounds used:
   5 terms and 8 rounds, 3 terms and 10, 2 terms and 24; the ninth's
   explorations for the comparison at its own bounds (8, 9 and 12 rounds);
   reachability at 3 terms and 4 rounds (the plan's target). The two-term run's
   24 rounds hold 86 201 results; the seed's 100 rounds with two terms hold
   31 391 855, given by the closed form.

9. **A first version of the reachability search left the results of the last
   round without edges, and disagreed with the criterion on 580 pairs at a small
   bound; the search now performs every result's changes, whatever its round.**
   Reason: a result of the last round was never expanded, so the search could
   not leave it; the path the criterion uses stays within the results of the
   exploration (its cost and terms never exceed those of its ends), so edges
   among them decide every pair.

10. **Reading C-J3 turned out to make a change of a result depend on the state
    taken (identifying two terms carrying pairs asserted together off the
    diagonal leaves them on the diagonal, where C-J3 does not take them out), so
    C-J3 is computed under C-X′ and its C-X consequence (an infinite round 3) is
    proved by a witness.** Found while writing `readings.py`.

11. **`ci/prose_watchlist.json` pins one hit of this paper, a two-word term the
    watchlist tags as an algorithms term, in its final section (§11, nearest
    known results).** Reason: the watchlist
    census counts it; `--regen` refuses in this sparse checkout (the omitted
    `meta/` files would lose their pins), so the one entry was added by hand with
    the digest `--probe` reports. Every other outside name of §11 is unwatched.

12. **The paper and ledger first cited the ninth's Lean theorem for jointly free
    parts by its name; `ci/check_axiom_citations.py` requires every cited Lean
    name in this derivation's own report, and that theorem lives in `lean4/`,
    so it is now cited by its claim ID (9:D5).** An injection test of the orbit
    count's divisibility guard first chose inputs whose total stayed divisible;
    it now uses three terms.

13. **Every earlier derivation's evidence was re-checked with its `--check`
    after this derivation's code was in place** (`research/twentysecond/check_earlier.py`);
    the outcome is recorded in the commit message.

14. **(Recorded by the twenty-third derivation.) `lean4_core/lakefile.toml` gained
    a second library, `Twentythird`, and lists it among the default targets.**
    Reason: `prompt/twentythird/prompt.md` puts the twenty-third's Lean library in
    this package, importing `Twentysecond`. The library `Twentysecond`, its files
    and its axiom report are unchanged; `lake build Twentysecond` builds exactly
    what it built before.

15. **(Recorded by the twenty-fourth derivation.) `lean4_core/lakefile.toml` gained
    a third library, `Twentyfourth`, appended to the default targets.** Reason:
    `prompt/twentyfourth/prompt.md` puts the twenty-fourth's Lean library in this
    package, importing `Twentythird`. Nothing already in the file was reordered,
    reworded or reformatted; the libraries `Twentysecond` and `Twentythird`, their
    files and their axiom reports are unchanged.
15. **(Recorded by the twenty-fifth derivation.) `lean4_core/lakefile.toml`
    gained a library, `Twentyfifth`, appended after the others, and its name was
    appended to the list of default targets.** Reason:
    `prompt/twentyfifth/prompt.md` puts the twenty-fifth's Lean library in this
    package, importing `Twentythird` (and through it `Twentysecond`). Nothing
    already in the lakefile was reordered or reworded; the libraries
    `Twentysecond` and `Twentythird`, their files and their axiom reports are
    unchanged.
