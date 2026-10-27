#!/usr/bin/env python3
"""Validate the focused manuscript's sole BibTeX database."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "build"
PAPER = ROOT / "paper"
DRIVER = PAPER / "spherical-regge-scissors.tex"
BIBLIOGRAPHY = PAPER / "biblio.bib"
ENTRY = re.compile(r"^\s*@[A-Za-z]+\s*\{\s*([^,\s]+)\s*,", re.MULTILINE)
CITATION = re.compile(r"\\(?:cite|nocite)(?:\s*\[[^]]*\])*\s*\{([^}]*)\}")


def main() -> int:
    failures: list[str] = []
    database = BIBLIOGRAPHY.read_text(encoding="utf-8")
    keys = ENTRY.findall(database)

    exact_duplicates = sorted({key for key in keys if keys.count(key) > 1})
    folded: dict[str, list[str]] = {}
    for key in keys:
        folded.setdefault(key.casefold(), []).append(key)
    folded_duplicates = sorted(
        values for values in folded.values() if len(values) > 1
    )
    if exact_duplicates:
        failures.append(f"duplicate BibTeX keys: {exact_duplicates}")
    if folded_duplicates:
        failures.append(f"case-colliding BibTeX keys: {folded_duplicates}")

    driver = DRIVER.read_text(encoding="utf-8")
    if r"\bibliography{paper/biblio}" not in driver:
        failures.append("driver does not select paper/biblio.bib")
    if r"\bibliographystyle{" not in driver:
        failures.append("driver has no BibTeX style declaration")

    available = set(keys)
    cited: set[str] = set()
    tex_sources = sorted(PAPER.rglob("*.tex"))
    for source_path in tex_sources:
        source = source_path.read_text(encoding="utf-8")
        relative = source_path.relative_to(ROOT)
        if r"\begin{thebibliography}" in source:
            failures.append(f"{relative}: inline thebibliography remains")
        for match in CITATION.finditer(source):
            cited.update(item.strip() for item in match.group(1).split(","))

    cited.discard("*")
    missing = sorted(cited - available)
    unused = sorted(available - cited)
    if missing:
        failures.append(f"missing citation keys: {missing}")
    if unused:
        failures.append(f"unused bibliography entries: {unused}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(
        f"Bibliography check: {len(keys)} unique entries exactly cover "
        f"{len(cited)} cited keys in {len(tex_sources)} TeX files"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
