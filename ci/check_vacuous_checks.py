"""Gate: a differential check must not compare a value with itself.

An OEWAS tripwire (see `ci/OEWAS_GATES.md`).  A *differential check* earns
its keep by comparing two INDEPENDENTLY computed quantities that agree on
correct code and disagree on a defect.  Several checks in the
tenth-fifteenth derivations instead compared a quantity with a copy of
ITSELF -- `admission_of_reaching(arrived)` against a `record` that was
`admission_of_reaching(out)` for the same state, `leftover_of(state, change)`
against a `leftover` that was `leftover_of(state, change)`.  Such a check can
never fire on a derivation defect; it tests only determinism.  Every coverage
and injection gate was green.  This gate catches the shape statically.

What it does.  It parses `code/**/*.py` and, in every function, resolves two
kinds of local alias:

  * **single assignment** -- `name = EXPR` (once, straight-line) aliases
    `name` to `EXPR`;
  * **generator unpacking** -- `for a, b, … in gen(...)`, where `gen` is a
    module-level generator that `yield`s a tuple, aliases each target to the
    corresponding yielded expression (in the generator's own names).

It then canonicalizes both operands of every `==`/`!=`/`is`/`is not`
comparison by substituting those aliases, and flags the comparison when the
two operands become syntactically identical -- a self-comparison.  This
catches the generator-routed cases above, because both operands canonicalize
to the same generator-namespace expression.

What it is NOT.  It resolves aliases one module deep, not across module
boundaries or through mutation, so a self-comparison assembled across files,
or one where the two sides are provably-equal-but-not-syntactically-identical
(a wrapper that returns its delegate's value unchanged), is missed -- that is
the job of the dynamic "mutation must bite" layer specced in
`ci/OEWAS_GATES.md`.  A legitimate self-comparison (e.g. a NaN test) is
exempted with a trailing `# vacuous-ok: <reason>` comment.

Run: `python ci/check_vacuous_checks.py` (exit 1 on a hit), or `--report` to
list the comparisons it examined and their canonical forms.
"""

from __future__ import annotations

import argparse
import ast
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

_CMP = (ast.Eq, ast.NotEq, ast.Is, ast.IsNot)
_MAX_DEPTH = 8


@dataclass
class Generator:
    """A module-level generator and the tuple it yields (element ASTs)."""

    elements: list[ast.expr]


def module_generators(tree: ast.Module) -> dict[str, Generator]:
    """Every top-level `def` that yields a tuple, by name, with its yield elements."""
    gens: dict[str, Generator] = {}
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        for sub in ast.walk(node):
            if isinstance(sub, ast.Yield) and isinstance(sub.value, ast.Tuple):
                gens.setdefault(node.name, Generator(list(sub.value.elts)))
                break
    return gens


def _call_name(node: ast.expr) -> str | None:
    """The function name of a Call, `f(...)` or `mod.f(...)`."""
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            return node.func.attr
    return None


@dataclass
class Aliases:
    """Name -> defining expression, within one function."""

    table: dict[str, ast.expr] = field(default_factory=dict)
    multiply_assigned: set[str] = field(default_factory=set)

    def add(self, name: str, expr: ast.expr) -> None:
        if name in self.multiply_assigned:
            return
        if name in self.table:
            del self.table[name]
            self.multiply_assigned.add(name)
            return
        self.table[name] = expr


def collect_aliases(func: ast.FunctionDef, gens: dict[str, Generator]) -> Aliases:
    """Single-assignment and generator-unpack aliases of one function's locals."""
    aliases = Aliases()
    for node in ast.walk(func):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            aliases.add(node.targets[0].id, node.value)
        elif isinstance(node, ast.For) and isinstance(node.target, ast.Tuple):
            gen = gens.get(_call_name(node.iter) or "")
            if gen and len(gen.elements) == len(node.target.elts):
                for tgt, elem in zip(node.target.elts, gen.elements):
                    if isinstance(tgt, ast.Name):
                        aliases.add(tgt.id, elem)
    return aliases


class _Substitute(ast.NodeTransformer):
    """Replace aliased Names by their defining expressions, bounded and cycle-guarded."""

    def __init__(self, aliases: Aliases, depth: int, active: frozenset[str]) -> None:
        self.aliases = aliases
        self.depth = depth
        self.active = active

    def visit_Name(self, node: ast.Name) -> ast.expr:
        if self.depth <= 0 or node.id in self.active or node.id not in self.aliases.table:
            return node
        expr = self.aliases.table[node.id]
        substituted = _Substitute(self.aliases, self.depth - 1, self.active | {node.id}).visit(_clone(expr))
        assert isinstance(substituted, ast.expr)
        return substituted


def _clone(node: ast.expr) -> ast.expr:
    body = ast.parse(ast.unparse(node), mode="eval").body
    return body


def canonical(expr: ast.expr, aliases: Aliases) -> str:
    """The expression with aliases substituted, as a normalized string."""
    substituted = _Substitute(aliases, _MAX_DEPTH, frozenset()).visit(_clone(expr))
    return ast.unparse(ast.fix_missing_locations(substituted))


@dataclass(frozen=True)
class Hit:
    file: str
    line: int
    text: str
    canonical: str


def _exempt(source_lines: list[str], lineno: int) -> bool:
    line = source_lines[lineno - 1] if 0 < lineno <= len(source_lines) else ""
    return "# vacuous-ok" in line


def scan_source(source: str, rel: str) -> list[Hit]:
    """Self-comparisons in one module's source text."""
    lines = source.splitlines()
    tree = ast.parse(source)
    gens = module_generators(tree)
    hits: list[Hit] = []
    for func in ast.walk(tree):
        if not isinstance(func, ast.FunctionDef):
            continue
        aliases = collect_aliases(func, gens)
        for node in ast.walk(func):
            if not isinstance(node, ast.Compare) or len(node.ops) != 1 or not isinstance(node.ops[0], _CMP):
                continue
            left, right = node.left, node.comparators[0]
            if isinstance(left, ast.Constant) or isinstance(right, ast.Constant):
                continue
            cl, cr = canonical(left, aliases), canonical(right, aliases)
            if cl == cr and not _exempt(lines, node.lineno):
                hits.append(Hit(rel, node.lineno, ast.unparse(node), cl))
    return hits


def scan_file(path: Path) -> list[Hit]:
    """Self-comparisons in one module."""
    return scan_source(path.read_text(encoding="utf-8"), path.relative_to(REPO).as_posix())


def code_files(code_root: Path) -> list[Path]:
    return sorted(p for p in code_root.rglob("*.py") if "__pycache__" not in p.parts)


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(prog="check_vacuous_checks", description=__doc__)
    parser.add_argument("--code", type=Path, default=REPO / "code")
    parser.add_argument("--report", action="store_true", help="list every comparison and its canonical operands")
    args = parser.parse_args(argv)

    files = code_files(args.code)
    if args.report:
        for path in files:
            tree = ast.parse(path.read_text(encoding="utf-8"))
            gens = module_generators(tree)
            for func in ast.walk(tree):
                if not isinstance(func, ast.FunctionDef):
                    continue
                aliases = collect_aliases(func, gens)
                for node in ast.walk(func):
                    if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], _CMP):
                        cl = canonical(node.left, aliases)
                        cr = canonical(node.comparators[0], aliases)
                        mark = "  <-- SELF" if cl == cr else ""
                        print(f"{path.relative_to(REPO).as_posix()}:{node.lineno}: {cl} {'==/!=' } {cr}{mark}")
        return 0

    hits = [h for path in files for h in scan_file(path)]
    if not hits:
        print(f"vacuous-check gate clean: {len(files)} modules scanned, no self-comparison")
        return 0
    for h in hits:
        print(
            f"FAIL: {h.file}:{h.line}: `{h.text}` compares a value with itself "
            f"(both sides are `{h.canonical}`) -- compare against an independent oracle, "
            f"or mark `# vacuous-ok: <reason>` if intended"
        )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
