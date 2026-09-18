"""`python code/generate_third.py [options]`: the same as `python -m third` with `code/` on the path."""

from third.__main__ import main

if __name__ == "__main__":
    raise SystemExit(main())
