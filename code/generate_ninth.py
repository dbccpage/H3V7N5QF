"""`python code/generate_ninth.py [options]`: the same as `python -m ninth` with `code/` on the path."""

from ninth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
