"""`python code/generate_sixteenth.py [options]`: the same as `python -m sixteenth` with `code/` on the path."""

from sixteenth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
