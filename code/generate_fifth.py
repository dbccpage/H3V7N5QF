"""`python code/generate_fifth.py [options]`: the same as `python -m fifth` with `code/` on the path."""

from fifth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
