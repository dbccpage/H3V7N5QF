"""`python code/generate_fourth.py [options]`: the same as `python -m fourth` with `code/` on the path."""

from fourth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
