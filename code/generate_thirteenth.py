"""`python code/generate_thirteenth.py [options]`: the same as `python -m thirteenth` with `code/` on the path."""

from thirteenth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
