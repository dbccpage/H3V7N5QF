# Whole-repo review findings

This file is outside the derivational seal. Severity: **critical** means a
false claim or false proof status; **major** means an unsupported claim or
vacuous check; **minor** means presentation or process. Candidate hits from
`audit_ledger.py` are not findings until the cited Lean names and claim
scope have been checked.

**Repair disposition (computed):** F001–F013 were repaired on the separate
local repair branch in commit
`e5d02ddab4373a7c35eb0eaafad7b9972234d01d`. F001–F010 received the
missing `#print axioms` requests, regenerated reports and manifests, and an
injection-tested citation/report gate. F011–F012 now read their values from
the actual change/admission models, with injection tests that alter those
models. F013's eight carry-forward cells now point to their existing source
or generated series. These changes do not assert new theorems or extend the
finite bounds. The full exact-commit suite passed 52/52 commands at that
commit, recorded in `repair_suite/summary.json`; the sections below retain the
original defect evidence.

## F001 — seventeenth axiom report omits cited parent theorems

- **Derivation:** seventeenth.
- **File:line:** `paper/seventeenth/paper.md:340–349` (parent-theorem
  comparison), `paper/seventeenth/claim_ledger.md:48,72,78–79`,
  `lean4/Seventeenth/Axioms.lean:12–58`.
- **Defect class:** cited Lean theorems missing from the derivation's own
  axiom report.
- **Severity:** major (the report is incomplete as a receipt for claims
  that cite parent proofs; this does not refute those theorems).
- **Evidence:** the paper or ledger cites `given_distinct`,
  `two_states_on_given_terms`, `adding_xrx_always_obstructed`,
  `Step.legal`, `Reach.legal`, `Reach.arb_gone_for_good`,
  `fewest_changes_A`, `fewest_changes_B`, `identify_legal_iff`,
  `remove_obstruction_first_or_last`, `bra_not_derived`, and
  `bra_not_refuted` among its re-checks. The
  committed `evidence/seventeenth/lean_axioms.txt` has no lines for these 12
  names. They exist in the base Lean source and are printed in the base
  `evidence/lean_axioms.txt`.
- **Proposed repair:** add the actually cited parent theorems to
  `lean4/Seventeenth/Axioms.lean`, regenerate its axiom report and manifest,
  and add a narrow citation-to-report detector only if the same defect is
  confirmed in another derivation. No theorem statement is changed.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F003 — second report omits cited base theorems

- **Derivation:** second.
- **File:line:** `paper/second/paper.md:197–275`,
  `paper/second/claim_ledger.md:44–50`, `lean4/Second/Axioms.lean`.
- **Defect class:** cited Lean theorems missing from own axiom report.
- **Severity:** major.
- **Evidence:** the citations to `Reach.legal`, `Reach.nonempty`,
  `Reach.wf`, `givenA_to_givenB`, `givenB_to_givenA`, `reach_by_edits`,
  and `remove_legal` do not appear in `evidence/second/lean_axioms.txt`.
  The base Lean files declare them.
- **Proposed repair:** print those base theorems in the second report source
  and regenerate its report and manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F004 — third report omits the cited second size bound

- **Derivation:** third.
- **File:line:** `paper/third/claim_ledger.md:55`,
  `lean4/Third/Axioms.lean`.
- **Defect class:** cited Lean theorem missing from own axiom report.
- **Severity:** major.
- **Evidence:** the re-check names `Step3.size_le`; the second source
  declares it, but the third report does not print it.
- **Proposed repair:** add that parent theorem to the third report and
  regenerate its report and manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F005 — fourth report omits cited parent theorems

- **Derivation:** fourth.
- **File:line:** `paper/fourth/paper.md:267,347`,
  `paper/fourth/claim_ledger.md:55,61`, `lean4/Fourth/Axioms.lean`.
- **Defect class:** cited Lean theorems missing from own axiom report.
- **Severity:** major.
- **Evidence:** `Step2.size_eq`, `additions_count`,
  `givenA_to_givenB2`, and `givenB_never_givenA` are cited parent results
  absent from the fourth report.
- **Proposed repair:** print these resolved parent theorems and regenerate
  the fourth report and manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F006 — fifth report omits a cited base potential bound

- **Derivation:** fifth.
- **File:line:** `paper/fifth/paper.md:901`, `lean4/Fifth/Axioms.lean`.
- **Defect class:** cited Lean theorem missing from own axiom report.
- **Severity:** major.
- **Evidence:** the paper cites the base `Reach.costA_le`; it exists in
  `lean4/H3V7N5QF/Cost.lean`, but is absent from the fifth report.
- **Proposed repair:** print this theorem and regenerate the fifth report
  and manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F007 — sixth report omits cited containment and identification proofs

- **Derivation:** sixth.
- **File:line:** `paper/sixth/paper.md:216,624`,
  `paper/sixth/claim_ledger.md:51,119`, `lean4/Sixth/Axioms.lean`.
- **Defect class:** cited Lean theorems missing from own axiom report.
- **Severity:** major.
- **Evidence:** `step_identify_given` is declared in `Sixth/Step.lean`,
  and `contains_fails` in `Fifth`; neither is in the sixth report.
- **Proposed repair:** print both and regenerate the sixth report and
  manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F008 — eighth report omits a cited sixth upper-bound theorem

- **Derivation:** eighth.
- **File:line:** `paper/eighth/paper.md:293`,
  `paper/eighth/claim_ledger.md:54`, `lean4/Eighth/Axioms.lean`.
- **Defect class:** cited Lean theorem missing from own axiom report.
- **Severity:** major.
- **Evidence:** `reach6_raise` is declared in the sixth Lean source and
  cited as a re-check, but absent from the eighth report.
- **Proposed repair:** print it and regenerate the eighth report and
  manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F009 — fifteenth report omits cited fourteenth witnesses

- **Derivation:** fifteenth.
- **File:line:** `paper/fifteenth/paper.md:113`,
  `paper/fifteenth/claim_ledger.md:38`, `lean4/Fifteenth/Axioms.lean`.
- **Defect class:** cited Lean theorems missing from own axiom report.
- **Severity:** major.
- **Evidence:** `twoBoth_remove_r` and `twoBoth_remove_s` exist in
  `Fourteenth` and support the ledger's comparison, but are not printed
  by the fifteenth report.
- **Proposed repair:** print them and regenerate the fifteenth report and
  manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F010 — sixteenth report omits two cited theorems

- **Derivation:** sixteenth.
- **File:line:** `paper/sixteenth/paper.md:187`,
  `paper/sixteenth/claim_ledger.md:40,51`, `lean4/Sixteenth/Axioms.lean`.
- **Defect class:** cited Lean theorems missing from own axiom report.
- **Severity:** major.
- **Evidence:** `remove_add9` and `Reach16.swap` are declared in the
  sixteenth source and cited by the paper/ledger, but the report prints
  neither. `Reach16.swap` is distinct from the printed `Step16.swap` and
  `reach16_swap`.
- **Proposed repair:** print both and regenerate the sixteenth report and
  manifest.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F002 — ninth axiom report omits cited eighth theorems

- **Derivation:** ninth.
- **File:line:** `paper/ninth/paper.md:300,306,350,382,399,498`,
  `paper/ninth/claim_ledger.md:63,66,68`, and the "Earlier derivations"
  section of `lean4/Ninth/Axioms.lean`.
- **Defect class:** cited Lean theorems missing from the derivation's own
  axiom report.
- **Severity:** major (the report is incomplete as a receipt for the
  comparison claims; no false theorem has been established).
- **Evidence:** `Step8.size_step`, `reach8_raise`, `Reach8.nonempty`,
  `reach8_of_names`, `cycle2_8`, `fewest_changes8_lower_A`, and
  `rename8_addTerm`, plus the fifth's `contains_fails`, are cited in the
  ninth paper or ledger, but their names are absent from
  `lean4/Ninth/Axioms.lean` and `evidence/ninth/lean_axioms.txt`. The parent
  Lean sources declare these names and their parent reports print them.
- **Proposed repair:** print the actually cited parent theorems in the
  ninth report source, regenerate the report and manifest, and add an
  injection-tested detector for report completeness.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F011 — eighth evidence writes literal relation attempt counts

- **Derivation:** eighth.
- **File:line:** `code/eighth/evidence.py:167–168`; the attempt count is
  discussed in `paper/eighth/paper.md:256,612–614`.
- **Defect class:** hard-coded values in evidence posing as computed counts.
- **Severity:** minor (the numbers agree at the recorded beginning, but the
  receipt would not change if the change enumeration drifted).
- **Evidence:** `of_which_in_r` is assigned `1 + int(bra) + 4` and
  `of_which_in_s` is assigned `4`. The same function already constructs the
  change list, which can supply both counts directly.
- **Proposed repair:** count `REMOVE` and `ADD_ASSERTION` changes by relation
  from `changes(start)` and test this against the closed form separately.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F012 — fifteenth evidence hard-codes admission availability

- **Derivation:** fifteenth.
- **File:line:** `code/fifteenth/evidence.py:182–183`.
- **Defect class:** hard-coded values in evidence.
- **Severity:** minor (admission availability is chosen in C-A1, so this is
  receipt drift rather than a false derived claim).
- **Evidence:** `can_admit_empty` and `can_admit_one` are literal `True`
  although the model has `can_admit(state)` in `code/fifteenth/admission.py`.
- **Proposed repair:** call that model function for both states and retain
  the paper's explicit "chosen, by construction" status.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.

## F013 — closed ledger carry-forwards leave their evidence cell blank

- **Derivations:** fourth, fifth, sixth, seventh, eighth, ninth.
- **File:line:** `paper/fourth/claim_ledger.md:130`,
  `paper/fifth/claim_ledger.md:131–132`,
  `paper/sixth/claim_ledger.md:126–127`,
  `paper/seventh/claim_ledger.md:120`,
  `paper/eighth/claim_ledger.md:120`,
  `paper/ninth/claim_ledger.md:136`.
- **Defect class:** evidence-custody omission in inherited closed/open-item rows.
- **Severity:** minor. The status or re-check cell names the earlier result,
  but the evidence column is `—`; this does not refute the cited result.
- **Evidence:** the eight rows say the multiplicity question is closed by
  the fourth seed or a round count is supplied by a series, and already
  name D10/D14 or a parent row elsewhere in the row. They do not point to
  that source from their evidence cell. Rows explicitly marked “without
  object” are excluded: they make no live claim requiring a proof receipt.
- **Proposed repair:** add the already named parent seed, own series claim,
  and generated round files in the evidence cells. Do not change the source
  status or claim strength.
- **Disposition:** repaired in `e5d02dd`; 52/52 exact-commit suite commands passed.
