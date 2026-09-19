"""`python code/generate_seventh.py [options]`: the same as `python -m seventh` with `code/` on the path."""

from seventh.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
