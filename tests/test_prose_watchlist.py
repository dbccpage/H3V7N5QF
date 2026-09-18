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


def test_in_scope_excludes_seed_inputs_and_the_json() -> None:
    # the whole prompt/ tree is read-only seed input, out of scope by prefix.
    assert not cpw.in_scope("prompt/second/seed_prompt.md")
    assert not cpw.in_scope("prompt/third/seed_prompt.md")
    assert not cpw.in_scope(cpw.WATCHLIST_REL)
    assert cpw.in_scope("paper/second/paper.md")


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
