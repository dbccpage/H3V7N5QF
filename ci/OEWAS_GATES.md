# OEWAS anti-skill gates

Two gates that catch a class of defect the other gates cannot: work that
passes coverage, typing, the watchlist and `lake build` **green** while a
paper over-claims. Both were harvested from real defects found reviewing the
tenth–fifteenth derivations, where fifteen such over-claims shipped under a
full set of green gates. A gate here is proved by **biting** — failing on the
exact defect, naming it, recovering when it is removed — not by being green
(`tests/test_oewas_gates.py` injection-proves each).

They are "anti-skill detectors": each names one *failure pattern* — a move
that looks like evidence and is not. They are deliberately **narrow and
domain-specific**. A detector that tries to find "wrongness" in general
overfits and fires on sound work; these fire on two precise,
mechanical shapes and are silent otherwise, and each documents exactly what
it does **not** see.

## Gate: vacuous self-comparison (`check_vacuous_checks.py`)

A *differential check* must compare two independently computed quantities.
Several checks instead compared a value with a copy of itself —
`admission_of_reaching(arrived)` against a `record` that was
`admission_of_reaching` of the same state; `leftover_of(state, change)`
against a `leftover` that was `leftover_of(state, change)`. Such a check
never fires on a derivation defect. The gate resolves local single-assignment
aliases **and one level of generator-yield unpacking**, then flags any
`==`/`!=`/`is` comparison whose two operands canonicalize to the same
expression. It catches the generator-routed shape that actually occurred,
because both operands reduce to the same generator-namespace expression.

Reach: it resolves aliases one module deep. A self-comparison assembled
across module boundaries, or one where two sides are provably-equal but not
syntactically identical after substitution (a wrapper returning its
delegate's value), is **not** caught statically — that is the dynamic layer
below.

## Gate: definitional citation (`check_definitional_citations.py`)

A ledger claim marked **derived** must not rest on a Lean theorem that proves
nothing about it. Two precise signals fail the gate:

- **self-equality** — the theorem's statement is `EXPR = EXPR`
  (`reaching = reaching`, `leftoverAdd = leftoverAdd`);
- **notion mismatch** — the theorem is proved by reflexivity and its
  statement never names the record notion (leftover / writing / record /
  coarse / admission) the claim is about (`no_third_rel` is about `proj`,
  cited for "the record is not a third multiplicity").

A reflexivity proof is **not** flagged on its own: "an addition leaves
nothing `:= rfl`" is true by computation and names its notion — a fair, if
definitional, derivation (surfaced by `--report`, not failed). A row that
discloses the weakness ("by construction", "definitional", "identity") is
exempt. Reach: it reads Lean *source*, not the elaborated proof, so a proof
definitional only after elaboration is missed; `#print axioms` would close
that at the cost of a Lean build.

## Gate: mutation must bite (`check_mutation_bite.py`)

The static self-comparison gate cannot see a vacuous check whose two sides
are equal by *computation* rather than by *syntax*. This dynamic gate closes
that: it is a **fitness assay** for the checks. For each registered
differential check it runs the derivation on a small exploration (the
baseline must be clean), perturbs a *derivation-specific* record function
(`admission_of_reaching`, `leftover_of`) **at every binding site**, and
requires the check's disagreement field to fire. A check whose two sides are
the same computation stays equal under the uniform perturbation -- it does not
bite -- and fails the gate; a check that uses an independent oracle or a
transformed argument bites and passes. It is injection-proven by
reconstructing a real vacuous check (the fifteenth's original cross-relation
form) and showing it survives where the repaired form bites.

This is mutation testing pointed at the checks: variation (the mutation) and
selection (the check that must kill the mutant). A check under no selective
pressure is unfit as a detector, whatever its coverage.

The panel is **complete over the check surface**: it enumerates every
list-valued field of each derivation's `*Check` dataclass (33 fields across
the tenth-fifteenth) and requires a bite case for each. A new disagreement
field with no bite case fails the gate as *uncovered*; a bite case naming a
field that no longer exists fails too. So a check cannot be added, or quietly
made vacuous, without the gate noticing. Differential fields (the vacuity
risk) are perturbed through their record function at every binding site; guard
fields (`assertion_records`, `cannot_admit`, ...) are perturbed through the
predicate that gates them -- each field is proven reachable by the mutation
designed to trigger it. The **antigen panel** is domain-specific by design and
maintained by hand; extending it to a new derivation is a new panel of the
same shape.

## Gate: cited Lean name in the derivation's own report (`check_axiom_citations.py`)

Whole-repo review F001–F010 found ten derivations whose paper or ledger
cited a Lean theorem missing from that derivation's `#print axioms` report.
The report writers had built successfully: a successful report command alone
did not certify *citation completeness*. This gate scans backticked names in
each paper and ledger, filters them against local Lean theorem/lemma
declarations, and requires each identified name in that derivation's actual
Lean-generated report. Its injection test removes the real second
derivation's `Seed.Reach.legal` line, checks that the gate fails, then restores
the line and checks a pass. This is an assay for one observed custody defect,
not a count of theorems.

Reach: short, unqualified names can collide; they are accepted by suffix.
Unbackticked prose references and declarations other than `theorem` or
`lemma` are outside the detector. The separate Lean report writer still
elaborates the names and checks the actual axiom dependencies. Neither
detector establishes that the cited theorem proves the English claim; the
claim ledger and definitional-citation review have that job.

## Where the design notes went

Two sections of design notes on how these detectors should grow stood here.
They are not a gate and not an input to any derivation, and on 2026-09-24
they moved to the review area (`paper/change_log.md` item 41). In short:
each detector is an executable check with an injection proof, grown from a
real defect, kept narrow, and never replaced by a paragraph in a prompt.
