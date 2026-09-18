"""`python code/generate_second.py [options]`: the same as `python -m second` with `code/` on the path."""

from second.__main__ import main

if __name__ == "__main__":
    raise SystemExit(main())
