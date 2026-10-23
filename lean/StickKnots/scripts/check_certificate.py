#!/usr/bin/env python3
"""Check project source and compile the public declaration/axiom audit."""

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def code_only(source: str) -> str:
    """Remove Lean's nested comments and strings before scanning tokens."""
    out = []
    i, depth = 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth:
            if source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def main() -> None:
    sources = [ROOT / "StickKnots.lean", *sorted((ROOT / "StickKnots").glob("*.lean"))]
    for path in sources:
        bad = re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", code_only(path.read_text()))
        if bad:
            raise SystemExit(f"Forbidden proof escape in {path.relative_to(ROOT)}: {bad}")
    entry = (ROOT / "StickKnots.lean").read_text()
    expected = set(re.findall(r"^#print axioms (\S+)", entry, re.MULTILINE))
    if not expected:
        raise SystemExit("The public entry point has no declaration audit.")
    result = subprocess.run(
        ["lake", "env", "lean", "StickKnots.lean"], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    status = re.compile(
        r"'(?P<name>StickKnots\.[^']+)' (?:depends on axioms:\s*\[(?P<axioms>[^]]*)\]"
        r"|does not depend on any axioms)"
    )
    observed = {}
    for match in status.finditer(result.stdout):
        axioms = {x.strip() for x in (match.group("axioms") or "").split(",") if x.strip()}
        if axioms - ALLOWED:
            raise SystemExit(f"Unexpected axiom in {match.group('name')}: {sorted(axioms - ALLOWED)}")
        observed[match.group("name")] = axioms
    if set(observed) != expected:
        raise SystemExit(f"Declaration audit mismatch: {sorted(set(observed) ^ expected)}")
    print(f"PASS: {len(sources)} Lean sources; {len(observed)} compiled declaration audits.")
    print("Only propext, Classical.choice, and Quot.sound are permitted.")
    print("External mathematics is passed as theorem hypotheses; this checks conditional proofs.")


if __name__ == "__main__":
    main()
