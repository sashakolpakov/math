#!/usr/bin/env python3
"""Rebuild the manuscript in an isolated path and compare PDF bytes."""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "build"
STEM = "spherical-regge-scissors"
BUILD_ENV = {
    "SOURCE_DATE_EPOCH": "1790467200",
    "FORCE_SOURCE_DATE": "1",
    "TZ": "UTC",
}
SOURCE_FILES = (
    "paper/spherical-regge-scissors.tex",
    "paper/macros.tex",
    "paper/biblio.bib",
    "paper/sections/01_statement.tex",
    "paper/sections/02_phase_charts.tex",
    "paper/sections/03_motivic_dictionary.tex",
    "paper/sections/04_relative_rigidity.tex",
    "paper/sections/05_specialization_scissors.tex",
)


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> int:
    env = os.environ.copy()
    env.update(BUILD_ENV)
    expected_pdf = ROOT.parent / f"{STEM}.pdf"

    with tempfile.TemporaryDirectory(prefix="spherical-regge-scissors-") as raw:
        build_root = Path(raw)
        shutil.copyfile(ROOT / ".latexmkrc", build_root / ".latexmkrc")
        for relative in SOURCE_FILES:
            source_path = ROOT / relative
            target_path = build_root / relative
            target_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source_path, target_path)
        source = build_root / "paper" / f"{STEM}.tex"
        command = [
            "latexmk",
            "-silent",
            "-pdf",
            "-gg",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-outdir={(build_root / 'paper').resolve()}",
            str(source.resolve()),
        ]
        result = subprocess.run(
            command,
            cwd=build_root,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if result.returncode != 0:
            print(f"isolated latexmk build failed\n{result.stdout}", file=sys.stderr)
            return 1

        rebuilt_pdf = build_root / "paper" / f"{STEM}.pdf"
        expected = digest(expected_pdf)
        rebuilt = digest(rebuilt_pdf)
        if rebuilt != expected:
            print(
                "PDF SHA-256 mismatch\n"
                f"  checked in: {expected}\n"
                f"  rebuilt:    {rebuilt}",
                file=sys.stderr,
            )
            return 1
        print(f"{STEM}: reproducible ({expected})")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
