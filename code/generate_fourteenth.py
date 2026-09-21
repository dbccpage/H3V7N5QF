"""`python code/generate_fourteenth.py [options]`: the same as `python -m fourteenth` with `code/` on the path."""

from fourteenth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
