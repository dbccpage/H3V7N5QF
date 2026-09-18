"""`python code/generate.py [options]`: the same as `python -m xry` with `code/` on the path."""

from xry.__main__ import main

if __name__ == "__main__":
    raise SystemExit(main())
