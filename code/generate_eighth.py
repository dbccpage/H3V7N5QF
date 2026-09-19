"""`python code/generate_eighth.py [options]`: the same as `python -m eighth` with `code/` on the path."""

from eighth.__main__ import main

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
