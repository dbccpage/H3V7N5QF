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

## Template correction, 2026-10-23

AuthorityEffect: None.

The dated note above describes the retained packages and their original
template. The current `make_packages.py` template now names the repository
folders directly, without the nonexistent index reference. This changes only
future rendered text. The ten retained packages, installed `prompt/` inputs,
and `package_checks.json` have not been regenerated or edited.

Do not rerun the package generator over the retained records to apply this
correction. The focused tests render the text in memory and check that the
existing inputs and package files keep their bytes:

```text
python -m unittest discover -s meta/next_ten -p test_prompt_template.py -v
```

This is a regression test, not a new development gate or a fresh run of the
ten mini-implementations.
