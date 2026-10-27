#!/usr/bin/env python3
"""Check manuscript coverage by Lean declarations and external interfaces."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPER_ROOT = ROOT.parents[1] / "preprints" / "The-Spherical-Regge-Scissors-Theorem-October-27-2026" / "build"
FORMAL = ROOT
COVERAGE = FORMAL / "coverage.json"
MAP = FORMAL / "MANUSCRIPT_MAP.md"
SECTION_DIR = PAPER_ROOT / "paper" / "sections"
ENVIRONMENT = re.compile(
    r"\\begin\{(?P<kind>definition|lemma|proposition|theorem|corollary)\}"
    r"(?:(?!\\end\{(?P=kind)\}).)*?"
    r"\\label\{(?P<label>[^}]+)\}",
    re.DOTALL,
)
DECLARATION = re.compile(
    r"\b(?:abbrev|def|structure|class|theorem|lemma|example)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)
FIELD = re.compile(r"^\s{2}(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*:", re.MULTILINE)
KINDS = {"lean", "external", "mixed", "definition"}


def manuscript_items() -> dict[str, tuple[str, str]]:
    found: dict[str, tuple[str, str]] = {}
    for path in sorted(SECTION_DIR.glob("*.tex")):
        source = path.read_text(encoding="utf-8")
        for match in ENVIRONMENT.finditer(source):
            label = match.group("label")
            if label in found:
                raise ValueError(f"duplicate labeled proof item: {label}")
            found[label] = (match.group("kind"), path.relative_to(PAPER_ROOT).as_posix())
    return found


def lean_names() -> set[str]:
    names: set[str] = set()
    for path in sorted(FORMAL.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        source = path.read_text(encoding="utf-8")
        for pattern in (DECLARATION, FIELD):
            for match in pattern.finditer(source):
                name = match.group("name")
                names.add(name)
                names.add(name.rsplit(".", 1)[-1])
    return names


def short_name(qualified: str) -> str:
    return qualified.rsplit(".", 1)[-1]


def main() -> int:
    failures: list[str] = []
    try:
        data = json.loads(COVERAGE.read_text(encoding="utf-8"))
        map_text = MAP.read_text(encoding="utf-8")
        manuscript = manuscript_items()
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(f"Cannot load formal coverage data: {error}", file=sys.stderr)
        return 1

    if data.get("schema") != 1 or not isinstance(data.get("items"), list):
        print("formal/coverage.json has an unsupported schema.", file=sys.stderr)
        return 1

    declared = lean_names()
    entries: dict[str, dict[str, object]] = {}
    for index, raw in enumerate(data["items"]):
        if not isinstance(raw, dict):
            failures.append(f"coverage item {index} is not an object")
            continue
        label = raw.get("label")
        kind = raw.get("kind")
        targets = raw.get("targets")
        explanation = raw.get("explanation")
        if not isinstance(label, str) or not label:
            failures.append(f"coverage item {index} has no label")
            continue
        if label in entries:
            failures.append(f"duplicate coverage entry: {label}")
            continue
        entries[label] = raw
        if kind not in KINDS:
            failures.append(f"{label}: invalid coverage kind {kind!r}")
        if not isinstance(targets, list) or not targets or not all(
            isinstance(target, str) and target for target in targets
        ):
            failures.append(f"{label}: targets must be a nonempty string list")
            targets = []
        if not isinstance(explanation, str) or not explanation.strip():
            failures.append(f"{label}: missing explanation")
        for target in targets:
            if short_name(target) not in declared:
                failures.append(f"{label}: unknown Lean target {target}")
            if target not in map_text and short_name(target) not in map_text:
                failures.append(f"{label}: target absent from MANUSCRIPT_MAP.md: {target}")
        if label not in map_text:
            failures.append(f"{label}: absent from MANUSCRIPT_MAP.md")

    missing = sorted(set(manuscript) - set(entries))
    extra = sorted(set(entries) - set(manuscript))
    if missing:
        failures.append(f"unclassified manuscript proof items: {missing}")
    if extra:
        failures.append(f"coverage entries without manuscript items: {extra}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    counts = {kind: 0 for kind in sorted(KINDS)}
    for entry in entries.values():
        counts[str(entry["kind"])] += 1
    detail = ", ".join(f"{kind}={counts[kind]}" for kind in sorted(counts))
    print(f"Formal coverage: {len(entries)} manuscript items classified ({detail})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
