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
domain-specific**. An immune system that tries to detect "wrongness" in
general overfits and fires on healthy tissue; these fire on two precise,
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
pressure is unfit as a detector, whatever its coverage. The registry is the
**antigen panel** -- domain-specific by design, maintained by hand; it
currently covers the three checks that had vacuous forms (tenth, fourteenth,
fifteenth). The next tightening is to enumerate every disagreement field and
require a bite case per field, so an unregistered check cannot hide.

## Anti-skills are detectors, not encyclopedia entries

The reason a hand-written skill/anti-skill library becomes an unfileable pile
is that it stores knowledge **generatively** -- as descriptions of good and
bad patterns, which cannot be enumerated, organized, or scoped to a domain. A
biological immune system has the same problem and does not solve it by
cataloguing pathogens; it stores **antibodies** -- detectors -- and grows them
from exposure. These gates follow that: an anti-skill here is never a
paragraph, it is an executable assay with an injection proof that it fires on
the real defect and stays silent on healthy code. Detectors are
*discriminative*, not generative -- you never enumerate all the ways to be
wrong, you only recognize a specific wrong when it appears -- and each domain
carries its own **antigen panel**, grown from that domain's real defects. The
filing system is the gate structure itself: detector + injection proof +
panel. That is where a skill/anti-skill goes; it does not go in a prompt.

## On growing this into OEWAS without forcing it

These are the first two entries in what could become a registry of anti-skill
detectors. The temptation is to impose a categorical scheme first — declare
the detectors an operad, look for instances. That overfits: an immune system
that starts from the abstraction fires on shapes the abstraction predicts,
not on the pathogens the corpus actually carries. The blind-derivation ethos
applies to the immune system too — **do not target a known structure.** Grow
detectors from observed defects (both of these came from real over-claims),
keep each narrow and domain-specific, and *let* compositional structure
appear if it is there: if a detector for "vacuous check *inside* a
definitional-citation context" turns out to be the composite of these two,
that composition is evidence of an operadic skeleton — earned, not assumed.
Until a composite detector is needed by a real defect, there is nothing to
compose, and forcing one would be the anti-skill this system exists to catch.
