"""`python code/lean_report_seventeenth.py`: the same as `python -m seventeenth.leanreport` with `code/` on the path."""

from seventeenth.leanreport import main

__all__ = ["main"]

if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
