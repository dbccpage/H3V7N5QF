"""The prose watchlist census (``ci/check_prose_watchlist.py``).

The repository has no hosted CI, so this test IS the gate: `python -m pytest`
runs the census over the tracked tree and fails if an outside-theory term
appears anywhere its pin does not already record it. These tests use NEUTRAL
probe words only; the real watched terms live as digests in
``ci/prose_watchlist.json`` and must not be written here as prose, which is the
whole point of storing them as digests.
"""

from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "ci"))

import check_prose_watchlist as cpw  # noqa: E402


def _watched(*terms: str) -> dict[str, str]:
    return {cpw.digest(t): "probe" for t in terms}


# -- normalization, tokenization, stemming ------------------------------


def test_normalize_strips_case_and_combining_marks() -> None:
    assert cpw.normalize("AepFel") == "aepfel"
    assert cpw.normalize("Zopf") == "zopf"
    assert cpw.normalize(cpw.normalize("Eclair")) == cpw.normalize("Eclair")


def test_digest_is_sha256_of_normalized_form() -> None:
    want = hashlib.sha256(b"zopf").hexdigest()
    assert cpw.digest("ZOPF") == want and cpw.digest("zopf") == want


def test_tokens_skip_identifiers_and_split_on_hyphen() -> None:
    # snake_case and digit-bearing names are single \w runs (no \b inside),
    # so they yield nothing; a hyphen is a separator; camelCase lowercases.
    assert cpw.tokens("alpha_beta gammaDelta eps-iota k9x") == [
        "gammadelta",
        "eps",
        "iota",
    ]


def test_stems_offer_singular_forms() -> None:
    assert cpw.stems("zzboxes") == ["zzboxes", "zzbox", "zzboxe"]
    assert cpw.stems("zzprobes") == ["zzprobes", "zzprobe"]
    assert cpw.stems("zzprobe") == ["zzprobe"]
    assert cpw.stems("abs") == ["abs"]


def test_es_strip_does_not_reach_a_three_letter_stem_through_a_vowel() -> None:
    # a word like "zopes" must not be es-stripped to a watched "zop".
    assert cpw.scan_text("zopes zope", _watched("zop")) == []
    assert len(cpw.scan_text("zops zop", _watched("zop"))) == 2


# -- scanning, census, comparison ---------------------------------------


def test_scan_finds_unigrams_and_bigrams_whole_word() -> None:
    watched = _watched("zzalpha", "zz beta")
    hits = cpw.scan_text("a zzalpha here\nzzalphas and zz beta too", watched)
    surfaces = sorted(h.surface for h in hits)
    assert surfaces == ["zz beta", "zzalpha", "zzalphas"]
    # a watched word inside an identifier is not split, so it does not hit.
    assert cpw.scan_text("x_zzalpha_y zzalpha9", watched) == []


def test_census_counts_per_file_per_digest() -> None:
    hits = {"a.md": cpw.scan_text("zzalpha zzalpha", _watched("zzalpha"))}
    census = cpw.census_of(hits)
    assert list(census["a.md"].values()) == [2]


def test_compare_fails_in_both_directions() -> None:
    d = cpw.digest("zzalpha")
    assert cpw.compare({"a.md": {d: 1}}, {"a.md": {d: 2}})[0].startswith("FAIL: NEW HIT")
    assert cpw.compare({"a.md": {d: 2}}, {"a.md": {d: 1}})[0].startswith("FAIL: STALE PIN")
    assert cpw.compare({"a.md": {d: 1}}, {"a.md": {d: 1}}) == []


def test_probe_reports_watched_status() -> None:
    watched = _watched("zzalpha")
    assert "WATCHED" in cpw.probe(["zzalpha"], watched)[0]
    assert "not watched" in cpw.probe(["zzbeta"], watched)[0]


def test_in_scope_counts_prompts_and_excludes_the_json() -> None:
    # since the author's ruling of 2026-09-25 the prompt/ tree is counted.
    assert cpw.in_scope("prompt/second/seed_prompt.md")
    assert cpw.in_scope("prompt/third/prompt.md")
    assert not cpw.in_scope(cpw.WATCHLIST_REL)
    assert cpw.in_scope("paper/second/paper.md")


def test_a_watched_word_in_a_prompt_is_counted(tmp_path: Path) -> None:
    # injection for the scope change: the same probe word is found in a prompt.
    rel = "prompt/probe/prompt.md"
    (tmp_path / "prompt" / "probe").mkdir(parents=True)
    (tmp_path / rel).write_text("line one\nuses zebrafinch here\n", encoding="utf-8")
    hits = cpw.scan_repo(tmp_path, _watched("zebrafinch"), files=[rel])
    assert [h.line for h in hits[rel]] == [2]


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


def _sparse_repo(tmp_path: Path) -> Path:
    """A two-file repository with `kept/a.md` present and `gone/b.md` marked
    skip-worktree and absent, as a sparse checkout leaves it."""
    repo = tmp_path / "r"
    (repo / "kept").mkdir(parents=True)
    (repo / "gone").mkdir()
    (repo / "kept" / "a.md").write_text("zebrafinch\n", encoding="utf-8")
    (repo / "gone" / "b.md").write_text("zebrafinch zebrafinch\n", encoding="utf-8")
    _git(repo, "init", "-q")
    _git(repo, "add", "-A")
    _git(repo, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "t")
    _git(repo, "update-index", "--skip-worktree", "gone/b.md")
    (repo / "gone" / "b.md").unlink()
    return repo


def test_a_sparse_checkout_sets_aside_the_pins_it_does_not_hold(tmp_path: Path) -> None:
    repo = _sparse_repo(tmp_path)
    assert cpw.sparse_files(repo) == {"gone/b.md"}
    d = cpw.digest("zebrafinch")
    data: dict[str, object] = {
        "watched": {d: "probe"},
        "baseline": {"kept/a.md": {d: 1}, "gone/b.md": {d: 2}},
    }
    code, messages, _ = cpw.run(repo, data)
    assert code == 0, messages
    assert "1 pinned files lie outside this checkout" in messages[0]
    # a new hit in the part that is held still fails.
    (repo / "kept" / "a.md").write_text("zebrafinch zebrafinch\n", encoding="utf-8")
    code, messages, _ = cpw.run(repo, data)
    assert code == 1 and "NEW HIT: kept/a.md" in messages[0]


def test_regen_refuses_in_a_sparse_checkout(tmp_path: Path) -> None:
    repo = _sparse_repo(tmp_path)
    path = repo / "w.json"
    data: dict[str, object] = {"watched": {cpw.digest("zebrafinch"): "probe"}, "baseline": {}}
    out = cpw.regen(repo, path, data)
    assert out[0].startswith("regen: refused")
    assert not path.exists()


def test_load_rejects_malformed_watchlist(tmp_path: Path) -> None:
    bad = tmp_path / "w.json"
    bad.write_text('{"watched": {}, "baseline": {}}', encoding="utf-8")
    with pytest.raises(ValueError):
        cpw.load(bad)
    bad.write_text('{"watched": {"nothex": "t"}, "baseline": {}}', encoding="utf-8")
    with pytest.raises(ValueError):
        cpw.load(bad)


# -- the gate itself: the tracked tree obeys the pin --------------------


def test_the_tracked_tree_matches_its_pin() -> None:
    data = cpw.load(REPO / cpw.WATCHLIST_REL)
    code, messages, _ = cpw.run(REPO, data)
    assert code == 0, "\n".join(messages)


def test_an_outside_term_outside_its_pin_is_caught() -> None:
    # the gate must fail when a watched term appears where the pin has none.
    data = cpw.load(REPO / cpw.WATCHLIST_REL)
    watched = data["watched"]
    assert isinstance(watched, dict)
    some_digest = next(iter(watched))
    forged = {"paper/second/change_log.md": [cpw.Hit(1, "probe", some_digest)]}
    failures = cpw.compare(
        data["baseline"],  # type: ignore[arg-type]
        cpw.census_of(forged),
        forged,
    )
    assert any("NEW HIT" in f and "change_log.md" in f for f in failures)


def _repo_with(tmp_path: Path, files: dict[str, str]) -> Path:
    repo = tmp_path / "s"
    for rel, text in files.items():
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(text, encoding="utf-8")
    _git(repo, "init", "-q")
    _git(repo, "add", "-A")
    _git(repo, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "t")
    return repo


def test_a_snapshot_without_the_review_area_sets_its_pins_aside(tmp_path: Path) -> None:
    # a snapshot clone holds no file under meta/: those pins are not read.
    repo = _repo_with(tmp_path, {"kept/a.md": "zebrafinch\n"})
    assert cpw.omitted_prefixes(cpw.tracked_files(repo)) == ("meta/",)
    d = cpw.digest("zebrafinch")
    data: dict[str, object] = {
        "watched": {d: "probe"},
        "baseline": {"kept/a.md": {d: 1}, "meta/x.md": {d: 3}},
    }
    code, messages, _ = cpw.run(repo, data)
    assert code == 0, messages
    assert "1 pinned files lie outside this checkout" in messages[0]
    assert cpw.regen(repo, repo / "w.json", data)[0].startswith("regen: refused")


def test_a_pin_under_a_partly_tracked_review_area_is_still_checked(tmp_path: Path) -> None:
    # injection: with meta/ present, a pinned meta file that is gone still fails.
    repo = _repo_with(tmp_path, {"meta/y.md": "plain\n"})
    assert cpw.omitted_prefixes(cpw.tracked_files(repo)) == ()
    d = cpw.digest("zebrafinch")
    data: dict[str, object] = {"watched": {d: "probe"}, "baseline": {"meta/x.md": {d: 3}}}
    code, messages, _ = cpw.run(repo, data)
    assert code == 1 and "STALE PIN: meta/x.md" in messages[0]
