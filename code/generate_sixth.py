"""`python code/generate_sixth.py [options]`: the same as `python -m sixth` with `code/` on the path."""

from sixth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
