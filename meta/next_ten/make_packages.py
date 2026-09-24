"""Write ten proposal packages from exact parent seeds after prototyping.

This writes only under meta/next_ten and checks that each replacement occurs
once. Run `prototype.py` and `rank.py` first; the parent prompt tree is read
only. The output is a proposal, not an installed derivation.
"""

from __future__ import annotations

import difflib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

# Old and new are whole seed sentences (or a whole adjacent sentence span).
# Unmentioned bytes are preserved exactly from the parent.
EDITS: dict[str, tuple[str, str]] = {
    "C19": (
        "A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.",
        "A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; removing a term that names no assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. Removing a term that names no assertion deletes that term and nothing asserted.",
    ),
    "C21": (
        "Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.",
        "Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy` is a change only if `xry` is not asserted.",
    ),
    "C09": (
        "Nothing is given: to begin with there are no terms and nothing is asserted.",
        "Given: one change adding a term has been made, and its outcome is the beginning. Nothing else is given.",
    ),
    "C07": (
        "Two results that differ only in how their terms are written are the same result.",
        "Two results that differ only in how their terms are written are different results.",
    ),
    "C01": (
        "A refused change is recorded and changes nothing.",
        "A refused change is recorded and changes nothing. Its written form is kept with that result; the next attempt at the same written change is performed even if it makes some `xrx` asserted.",
    ),
    "C04": (
        "Nothing is given: to begin with there are no terms and nothing is asserted.",
        "Nothing is given: to begin with there are no terms and nothing is asserted. Each alternative begins with four changes available; each performed change uses one, an attempt with none available changes nothing, and every result records how many remain.",
    ),
    "C05": (
        "Two results that differ only in how their terms are written are different results.",
        "A reading names at most two terms and records the assertions between them. Two results are the same if every such reading gives the same record.",
    ),
    "C25": (
        "A recorded leftover `xℓy` may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion.",
        "Recorded leftovers are kept in the order they arise. Only the most recently recorded leftover may be admitted, adding the assertion `xry` or the assertion `xsy`; an unadmitted leftover is not an assertion.",
    ),
    "C11": (
        "Nothing left, a leftover that a later change of the four kinds can clear, and a leftover that none of them can, are three outcomes.",
        "Nothing left, a leftover that a sequence of at most two later changes of the four kinds can clear, and a leftover that no such sequence can clear, are three outcomes.",
    ),
    "C17": (
        "A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.",
        "A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; exchanging the relations. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. Exchanging the relations replaces every `xry` with `xsy` and every `xsy` with `xry`, preserving each multiplicity.",
    ),
}

DETAILS: dict[str, dict[str, str]] = {
    "C19": {
        "question": "Can a bare term be removed, and does that let a nonempty result return to the empty beginning?",
        "reading": "Chosen: a term is bare exactly when no asserted pair names it. Unchosen: deleting a named term also deletes its assertions; set aside because the new sentence restricts removal to a bare term.",
        "expected": "The empty beginning is reached again from a one-term result in two changes. Test how this new cycle affects cost and sequence counts.",
        "map": "The seventh state embeds unchanged; every old step is a new step. The new removal has no seventh-step image, but adding then removing a bare term projects to an identity path.",
        "lean": "Define a bare-term removal, prove it preserves counted assertions, exhibit the two-step cycle, then classify new reachability and cost without assuming monotonicity.",
        "bound": "At most three terms, at most six rounds initially; compare independent finite state count and exact frontier.",
    },
    "C21": {
        "question": "Which two-relation results become unreachable when each addition checks the other relation?",
        "reading": "Chosen: the guard is checked on the current ordered pair before the addition. Unchosen: check the whole relation after addition; keep it if it changes results.",
        "expected": "One term with both loops is not reached in three changes, while the ninth reaches it. Test whether identification can make both relations assert one pair later.",
        "map": "The guarded state is the ninth state. Each guarded step embeds into a ninth step; the reverse map is partial at cross-relation additions.",
        "lean": "Define guarded steps, embed them into ninth steps, prove the local guard, give a blocked pair witness, and test an identification bypass.",
        "bound": "At most three terms and three counted assertions, initially six rounds; independent finite census and exact frontier.",
    },
    "C09": {
        "question": "What changes when the beginning is the outcome of a given addition rather than the empty result?",
        "reading": "Chosen: the given change has already occurred before round zero. Unchosen: count it as round one; report both round conventions.",
        "expected": "The beginning has one term and no assertions. Test exact cost shifts and whether the empty state can be reached by later changes.",
        "map": "The state and all steps are ninth's; the root is ninth's one-term state. Re-check every result theorem relative to that root.",
        "lean": "Define the new root as the outcome of ninth's add-term step; prove its properties and characterize reachable states and shortest paths from it.",
        "bound": "At most three terms and three assertions, six rounds initially; compare ninth at the same root.",
    },
    "C07": {
        "question": "How do literal term writings interact with refusal of an obstructed change?",
        "reading": "Chosen: distinct written letterings are distinct results. Unchosen: quotient by consistent renaming; keep as the parent comparison.",
        "expected": "Refusal still prevents loop-producing changes; the written result set may split free-rewriting classes.",
        "map": "The twenty-first state and steps are unchanged; the quotient from written results to its results preserves steps, but a section may fail to preserve every writing.",
        "lean": "Define written identity and quotient, prove the step map and refusal invariant, and supply a strict splitting witness if one exists.",
        "bound": "At most three named terms and four rounds; count written states and free orbits independently.",
    },
    "C01": {
        "question": "Can a recorded refusal make the same attempted change perform later?",
        "reading": "Chosen: the record belongs to the result and stores a canonical written attempt. Unchosen: the record is an external log; retain and compare because it may collapse to the parent.",
        "expected": "A second attempt after refusal may assert a loop. Check whether this creates a result unavailable under the parent's first-attempt answer rules.",
        "map": "Forgetting the refusal record maps objects to seventeenth states; it does not map the override step to a parent performed step. Restrict to paths without an override for a step map.",
        "lean": "Define the refusal record and override step; prove record preservation under other changes and exhibit or refute a two-attempt difference.",
        "bound": "Two or three terms and at most four rounds; include the attempted-change record in the finite census.",
    },
    "C04": {
        "question": "Does a state-carried budget limit results beyond a simple study round cap?",
        "reading": "Chosen: a performed change consumes one, including a change yielding an old result. Unchosen: a refused or repeated attempt consumes one; compare both.",
        "expected": "No path performs more than four changes; test whether states at the same ninth round can have different remaining budgets.",
        "map": "Forgetting the budget maps objects and performed steps into ninth; the reverse section must choose a budget and may not preserve composition after exhaustion.",
        "lean": "Define budgeted states and steps; prove decreasing budget, a four-step upper bound, and a concrete path distinction.",
        "bound": "Budget fixed at four, at most three terms and four rounds; enumerate every budget tag and compare ninth states.",
    },
    "C05": {
        "question": "Does agreement of all two-term readings identify results that free rewriting kept distinct?",
        "reading": "Chosen: a reading is an ordered choice of zero, one, or two terms and records the induced assertions; equality compares sets of records. Unchosen: compare multisets of readings; keep if it differs.",
        "expected": "Find the smallest pair of distinct written results with identical local records, or refute such a pair within the bound.",
        "map": "The eighteenth state and steps stay fixed; only result equality changes. The quotient map is total on states but needs a congruence check on steps.",
        "lean": "Define local records and equivalence, prove reflexive/symmetric/transitive, then check whether a step descends to equivalence classes.",
        "bound": "At most four terms with yes/no assertions, exhaustive orbit and local-record counts; initial short rounds.",
    },
    "C25": {
        "question": "Does the order of unadmitted leftovers affect which one can be admitted?",
        "reading": "Chosen: the record is a sequence of written leftover occurrences, with newest at the end. Unchosen: equal pairs are indistinguishable and only multiplicities matter; compare.",
        "expected": "Two histories with the same sixteenth counts may admit different pairs if their last leftovers differ.",
        "map": "Forgetting order maps states to sixteenth's counted record; direct steps preserve it, while admission maps when it is allowed. A counted state has many ordered lifts.",
        "lean": "Define an ordered record, its count projection, admissible last-element step, and a same-count/different-next-step witness.",
        "bound": "At most two terms, three assertions/leftovers and six rounds; census order-tagged states independently.",
    },
    "C11": {
        "question": "Does allowing two later changes clear a leftover that one later change cannot?",
        "reading": "Chosen: the comparison restores the complete result, including term writing up to the stated sameness. Unchosen: only the asserted pairs must return; compare if it differs.",
        "expected": "Search for a two-step-only clearance; otherwise prove the one-step and two-step classifications coincide within a declared class.",
        "map": "The tenth state and four changes stay fixed; only the classification of the leftover is recomputed from two-step paths.",
        "lean": "Define two-step clearance from existing steps, show every one-step clearance is two-step when an identity extension exists or state the exception, and prove a witness criterion.",
        "bound": "At most three terms and two assertions per relation; enumerate every one- and two-step continuation.",
    },
    "C17": {
        "question": "What changes when exchanging the two relations is itself a step?",
        "reading": "Chosen: a swap counts as a change only when it changes the exact written state. Unchosen: allow a self-swap as a counted step; keep its path count separately.",
        "expected": "States may be reached sooner through a swap; in the quotient by rewriting, test whether the swap yields a genuinely new edge.",
        "map": "All ninth steps embed. The new swap is the existing ninth involution on states, not an old ninth single step in general; it maps to an ungraded reachability path only where found.",
        "lean": "Define swap as a new constructor, prove swap twice returns the state, and bound shortest cost when a swap is available.",
        "bound": "At most two terms, two counted assertions and four rounds; compare the old and new shortest paths.",
    },
}


def parent_seed(parent: str) -> Path:
    return ROOT / "prompt" / parent / "seed_prompt.md"


def make_prompt(item: dict[str, object], detail: dict[str, str], rank: int) -> str:
    parent = str(item["parent"])
    slug = str(item["slug"])
    return f"""# [opaque repository name]

## Task

This is a proposed blind derivation of `prompt/{parent}/seed_prompt.md`. Begin from this package's `seed_prompt.md`, which changes only the sentences shown in `diff.patch`. The question is: {detail['question']} Determine what follows and what does not. Do not assume the hypothesis in `why.md` is true.

Throughout:

1. record for every notion whether it was given, chosen, derived, computed, refuted, or left open;
2. state what does not follow, with two legal witnesses or an independence proof;
3. prove each necessity and impossibility by Lean or exhaustive enumeration over a declared finite space;
4. keep every non-isomorphic alternative unless a proof eliminates it, including readings of ambiguous sentences;
5. cite and re-check every earlier result used through a valid state/step map or a fresh computation.

Do not steer toward a known theory. Only the final section of the paper may name nearest known results. Keep `ci/check_prose_watchlist.py` clean. Use only this repository, with no network, other files, or questions. Do not modify `prompt/`. First append a plan and stopping conditions to `CLAUDE.md` and commit that plan alone if this proposal is later installed as a derivation.

## Folders

If installed, follow the five-file pattern in `docs/index/topics.md`: `code/<ordinal>/` (typed Python), `code/run_<ordinal>.py`, `tests/`, `lean4/<Ordinal>/`, `evidence/<ordinal>/` with byte-identical `--check`, and `paper/<ordinal>/` with `paper.md`, `claim_ledger.md`, and `change_log.md`. This numbered meta package is a proposal; it does not write into those folders.

## Gates

Every existing `ci/` gate and stopping check must pass: `python -m pytest -n auto`, `python code/xry/gate.py coverage.json` (at least 95 percent line and branch and full coverage of each evidence module), `python -m mypy`, the prose watchlist, the vacuous-check, definitional-citation, mutation-bite, and axiom-citation gates, `lake +leanprover/lean4:v4.33.1 -d lean4 build`, no `sorry`, `admit`, or declared `axiom`, `#print axioms` for every cited Lean theorem, and byte-identical evidence regeneration. Read each command's real exit code; do not infer a pass from piped output or a committed receipt.

## Done

Every notion and claim has its status and evidence or is open; alternatives are retained or excluded by proof; inherited results are re-checked; the exact bounded frontier and independent completeness count are recorded; all gates pass; `prompt/` is unchanged; and all intended files are committed. State the strongest defensible result, including a failed hypothesis if that is what the evidence shows.
"""


def make_plan(item: dict[str, object], detail: dict[str, str]) -> str:
    parent = str(item["parent"])
    return f"""# Proposed plan and stopping conditions

**Status: chosen proposal outside the derivational seal.** Parent: `prompt/{parent}/seed_prompt.md`. Only this package's seed and the parent are inputs for a future derivation. No result in this plan is a theorem of the proposed seed.

## Reading and alternatives

{detail['reading']}

## Questions to derive or refute

{detail['expected']}

## Rule-5 re-check

{detail['map']} Every inherited claim must be cited and checked on the new seed; a map of states alone is insufficient for a claim about paths.

## Phases

1. Write the notion/source-status table and list every unchosen reading, including the exact sentence declining it.
2. Implement typed bounded state, step, answer, sameness and exploration code. Attempt every change, fewest additions first, for at most 100 rounds. Export the exact frontier, an independent count, and comparison receipts against the parent.
3. Lean targets: {detail['lean']} Print axioms for every cited theorem. If a target cannot be closed within a bounded attempt, mark it open or prove it on paper with a separate check; do not silently weaken it.
4. Generate deterministic evidence twice and compare hashes. Write paper, ledger and change log with claim status, evidence and falsifier; put known-result names only in the final paper section.
5. Run all native gates, check `git diff --stat -- prompt/`, inspect `.lake` staging, and commit in small coherent checkpoints.

## Bounds and stopping

{detail['bound']} Raise the bound only if it completes in minutes on this machine. Stop after 100 rounds or earlier if no new bounded result appears. At most two full paper/ledger review passes after the first draft. Stop and report if a step requires network, a file outside the repository, a change to `prompt/`, or a question. Completion requires all tests, coverage, mypy, Lean, axiom citations, prose and evidence checks green, no unsupported claim, and a clean intended tree.
"""


def make_why(item: dict[str, object], score: float, detail: dict[str, str], rank: int) -> str:
    axes = ("H", "N", "R", "C", "M", "G", "L")
    values = item["scores"]
    assert isinstance(values, list)
    score_text = ", ".join(f"{axis}={value}" for axis, value in zip(axes, values, strict=True))
    return f"""# Rank {rank}: {item['slug']}

**Status: chosen proposal, not a derived result.** Parent: `prompt/{item['parent']}/seed_prompt.md`; candidate {item['id']}. Weighted score **{score:g}/100** ({score_text}); weights and ±50 percent sensitivity are in `../rubric.md` and `../ranking.json`. A tie shares its score; numeric rank is presentation order.

**Hypothesis, open:** {item['hypothesis']}

**Falsifier:** {item['falsifier']}

**Bounded pre-seed check:** {('`../prototype_results.json` contains a witness for this candidate.' if str(item['id']) in ('C19', 'C21') else 'Not among the four initial prototypes; the plan states the first bounded test.')} A bounded witness does not establish an unbounded theorem.

**Re-check cost and scope:** {detail['map']}

**Drop condition:** Drop or rewrite the proposal if its edited seed has an unresolved contradiction, if every new distinction sits only in an external log or chosen label, if the finite test finds the stated falsifier and no distinct claim remains, or if its required state/step map cannot be made precise without a third seed sentence.
"""


def main() -> None:
    assert (HERE / "prototype_results.json").is_file(), "run the prototypes first"
    items: list[dict[str, object]] = json.loads((HERE / "candidates.json").read_text(encoding="utf-8"))
    by_id = {str(item["id"]): item for item in items}
    ranking = json.loads((HERE / "ranking.json").read_text(encoding="utf-8"))
    selected = ranking["top_ten"]
    assert len(selected) == 10 and set(selected) == set(EDITS) == set(DETAILS)
    score_by_id = {str(row["id"]): float(row["score"]) for row in ranking["ranked"]}
    for rank, ident in enumerate(selected, 1):
        item = by_id[ident]
        detail = DETAILS[ident]
        original_path = parent_seed(str(item["parent"]))
        original = original_path.read_bytes()
        old, new = (part.encode("utf-8") for part in EDITS[ident])
        assert original.count(old) == 1, f"edit span is not unique: {ident}"
        edited = original.replace(old, new, 1)
        assert edited.replace(new, old, 1) == original
        folder = HERE / f"{rank:02d}-{item['slug']}"
        folder.mkdir(exist_ok=True)
        (folder / "seed_prompt.md").write_bytes(edited)
        before = original.decode("utf-8").splitlines(keepends=True)
        after = edited.decode("utf-8").splitlines(keepends=True)
        diff = "".join(difflib.unified_diff(
            before, after,
            fromfile=f"prompt/{item['parent']}/seed_prompt.md",
            tofile=f"meta/next_ten/{folder.name}/seed_prompt.md",
            n=0,
        ))
        assert diff and "@@" in diff
        (folder / "diff.patch").write_text(diff, encoding="utf-8", newline="\n")
        (folder / "prompt.md").write_text(make_prompt(item, detail, rank), encoding="utf-8", newline="\n")
        (folder / "plan.md").write_text(make_plan(item, detail), encoding="utf-8", newline="\n")
        (folder / "why.md").write_text(make_why(item, score_by_id[ident], detail, rank), encoding="utf-8", newline="\n")
    print(f"wrote {len(selected)} proposal packages from exact parent seeds")


if __name__ == "__main__":
    main()
