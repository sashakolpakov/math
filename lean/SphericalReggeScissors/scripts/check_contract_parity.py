#!/usr/bin/env python3
"""Require every Lean proof-contract field to be assigned to E1--E8."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from check_lean_source import remove_comments_and_strings


ROOT = Path(__file__).resolve().parents[1]
PAPER_ROOT = ROOT.parents[1] / "preprints" / "The-Spherical-Regge-Scissors-Theorem-October-27-2026" / "build"
LEAN = ROOT / "SphericalReggeScissors" / "ExternalInputs.lean"
CONTRACT = ROOT / "contract_map.json"
HUMAN_MAP = ROOT / "MANUSCRIPT_MAP.md"
MANUSCRIPT = PAPER_ROOT / "paper" / "sections" / "01_statement.tex"

TRUST_STRUCTURES = {
    "MotivicInputs",
    "CoproductBridge",
    "SpecializationInputs",
    "ScissorsInputs",
    "GeometricReggeInputs",
    "ProofContract",
}
ALLOWED_INPUTS = {f"E{index}" for index in range(1, 9)}
STRUCTURE = re.compile(r"^structure\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\b", re.MULTILINE)
FIELD = re.compile(r"^  (?P<name>[^\s:]+)\s*:", re.MULTILINE)


def lean_contract_fields(source: str) -> set[tuple[str, str]]:
    stripped = remove_comments_and_strings(source)
    starts = list(STRUCTURE.finditer(stripped))
    found: set[tuple[str, str]] = set()
    for index, match in enumerate(starts):
        structure = match.group("name")
        if structure not in TRUST_STRUCTURES:
            continue
        end = starts[index + 1].start() if index + 1 < len(starts) else len(stripped)
        body = stripped[match.start():end]
        for field in FIELD.finditer(body):
            found.add((structure, field.group("name")))
    return found


def main() -> int:
    try:
        source = LEAN.read_text(encoding="utf-8")
        data = json.loads(CONTRACT.read_text(encoding="utf-8"))
        human_map = HUMAN_MAP.read_text(encoding="utf-8")
        manuscript = MANUSCRIPT.read_text(encoding="utf-8")
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(f"Cannot load contract-parity inputs: {error}", file=sys.stderr)
        return 1

    failures: list[str] = []
    if data.get("schema") != 1 or not isinstance(data.get("groups"), list):
        print("formal/contract_map.json has an unsupported schema.", file=sys.stderr)
        return 1

    mapped: set[tuple[str, str]] = set()
    for index, raw in enumerate(data["groups"]):
        if not isinstance(raw, dict):
            failures.append(f"contract group {index} is not an object")
            continue
        structure = raw.get("structure")
        fields = raw.get("fields")
        inputs = raw.get("inputs")
        explanation = raw.get("explanation")
        if structure not in TRUST_STRUCTURES:
            failures.append(f"contract group {index}: invalid structure {structure!r}")
            continue
        if not isinstance(fields, list) or not fields or not all(
            isinstance(field, str) and field for field in fields
        ):
            failures.append(f"{structure}: fields must be a nonempty string list")
            continue
        if not isinstance(inputs, list) or not inputs or not all(
            item in ALLOWED_INPUTS for item in inputs
        ):
            failures.append(f"{structure}/{fields[0]}: invalid E1--E8 assignment")
        if not isinstance(explanation, str) or not explanation.strip():
            failures.append(f"{structure}/{fields[0]}: missing explanation")
        for field in fields:
            key = (structure, field)
            if key in mapped:
                failures.append(f"duplicate contract-field mapping: {structure}.{field}")
            mapped.add(key)
            qualified = f"{structure}.{field}"
            if (
                f"**{field}**" not in human_map
                and f"**{qualified}**" not in human_map
                and f"`{field}`" not in human_map
                and f"`{qualified}`" not in human_map
            ):
                failures.append(
                    f"{qualified}: absent from formal/MANUSCRIPT_MAP.md"
                )

    declared = lean_contract_fields(source)
    missing = sorted(declared - mapped)
    extra = sorted(mapped - declared)
    if missing:
        failures.append(f"unmapped Lean contract fields: {missing}")
    if extra:
        failures.append(f"mapped fields absent from Lean contract: {extra}")

    for item in sorted(ALLOWED_INPUTS):
        label = rf"\label{{cp:input-{item}}}"
        if label not in manuscript:
            failures.append(f"manuscript is missing the numbered input label {item}")
        if item not in human_map:
            failures.append(f"MANUSCRIPT_MAP.md does not mention {item}")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1

    print(
        "External-contract parity: "
        f"{len(mapped)} Lean fields assigned exhaustively to E1--E8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
