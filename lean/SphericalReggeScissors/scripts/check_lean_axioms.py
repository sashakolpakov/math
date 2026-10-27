#!/usr/bin/env python3
"""Compile the public Lean audit module and check every printed dependency."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT
AUDIT = FORMAL / "SphericalReggeScissors" / "AxiomAudit.lean"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
PRINT = re.compile(r"^\s*#print\s+axioms\s+([^\s]+)\s*$", re.MULTILINE)
STATUS = re.compile(
    r"'SphericalReggeScissors\.(?P<name>[^']+)' "
    r"(?:depends on axioms:\s*\[(?P<axioms>[^]]*)\]"
    r"|does not depend on any axioms)"
)


def main() -> int:
    try:
        source = AUDIT.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        print(f"Cannot read {AUDIT.relative_to(ROOT)}: {error}", file=sys.stderr)
        return 1

    expected = {name.removeprefix("SphericalReggeScissors.") for name in PRINT.findall(source)}
    if not expected:
        print("AxiomAudit.lean contains no #print axioms declarations.", file=sys.stderr)
        return 1

    result = subprocess.run(
        ["lake", "env", "lean", "SphericalReggeScissors/AxiomAudit.lean"],
        cwd=FORMAL,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        print(result.stdout, file=sys.stderr, end="")
        print("Lean entry-point compilation failed.", file=sys.stderr)
        return result.returncode or 1

    observed: dict[str, set[str]] = {}
    for match in STATUS.finditer(result.stdout):
        raw_axioms = match.group("axioms")
        observed[match.group("name")] = (
            {item.strip() for item in raw_axioms.split(",") if item.strip()}
            if raw_axioms is not None
            else set()
        )

    failures: list[str] = []
    missing = expected - set(observed)
    extra = set(observed) - expected
    if missing:
        failures.append(f"missing #print axioms output: {sorted(missing)}")
    if extra:
        failures.append(f"unexpected #print axioms output: {sorted(extra)}")

    for declaration, axioms in sorted(observed.items()):
        forbidden = axioms - ALLOWED_AXIOMS
        if forbidden:
            failures.append(
                f"{declaration}: forbidden or undocumented axioms "
                f"{sorted(forbidden)}"
            )

    if failures:
        print(result.stdout, file=sys.stderr, end="")
        print("\n".join(failures), file=sys.stderr)
        return 1

    used = sorted(set().union(*observed.values()) if observed else set())
    print(
        f"Lean entry point: {len(observed)} public declarations compiled; "
        f"documented axioms only ({', '.join(used) or 'none'})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
