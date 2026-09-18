"""Statements about a state, and witnesses that they do not follow (third seed).

Cited from the first and second derivations (`xry.follows`, `second.follows`)
and re-checked
    The statements and `verdict` are about states, not changes; they apply to
    any exploration.  The results of the third seed are those of the second
    (a theorem of the paper), so the same statements hold in every result;
    the verdicts are computed again from the third exploration.
"""

from __future__ import annotations

from second.follows import EXTRA, at_least_two_terms, verdicts

__all__ = ["EXTRA", "at_least_two_terms", "verdicts"]
