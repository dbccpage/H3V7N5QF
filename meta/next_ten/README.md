# The ten proposal packages

**Note, 2026-09-25: a path that does not exist here.** Eleven places cite
`docs/index/topics.md`: each package's `prompt.md`, in its "Folders"
section, and the template in `make_packages.py` that wrote them. This
repository has no `docs/` folder, and it never had that file. Do not look
for it.

- **What it referred to.** The phrasing was carried from another repository,
  where that path is a generated index of its five-file topic families. Each
  family is a subject's code, runner, tests, Lean proofs and output, under
  one stem.
- **What to read instead.** In these prompts the citation stands for the list
  of folders in the same sentence: `code/<ordinal>/`,
  `code/run_<ordinal>.py`, `tests/`, `lean4/<Ordinal>/`,
  `evidence/<ordinal>/` and `paper/<ordinal>/`.
- **Why the text stays as it is.** These prompts are the records of
  derivations already run (pull request #45). `verify_packages.py` pins each
  package's file list, and `package_checks.json` records it. So this note
  stands here, beside the packages, and not in them.

`../climbing/blindness.md` lists the same finding. The installed prompts of
the seventeenth through twenty-first derivations carry the same dead path;
they are records under `prompt/` and are left as they are too.
