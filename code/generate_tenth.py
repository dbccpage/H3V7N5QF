"""`python code/generate_tenth.py [options]`: the same as `python -m tenth` with `code/` on the path."""

from tenth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
