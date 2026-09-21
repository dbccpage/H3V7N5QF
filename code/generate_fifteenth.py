"""`python code/generate_fifteenth.py [options]`: the same as `python -m fifteenth` with `code/` on the path."""

from fifteenth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
