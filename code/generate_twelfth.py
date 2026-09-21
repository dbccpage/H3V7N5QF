"""`python code/generate_twelfth.py [options]`: the same as `python -m twelfth` with `code/` on the path."""

from twelfth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
