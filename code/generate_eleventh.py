"""`python code/generate_eleventh.py [options]`: the same as `python -m eleventh` with `code/` on the path."""

from eleventh.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
