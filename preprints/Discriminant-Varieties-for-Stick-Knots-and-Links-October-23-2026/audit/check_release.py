#!/usr/bin/env python3
"""Verify the prepared StickNumbers artifact tree without a Lean cache."""

import argparse
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import unquote

from pypdf import PdfReader


PAPER = "Discriminant-Varieties-for-Stick-Knots-and-Links-October-23-2026"
SENSITIVE = re.compile(
    r"/(?:Users|home)/|[A-Za-z]:\\Users\\|sk-[A-Za-z0-9]{20,}|"
    r"gh[pousr]_[A-Za-z0-9]{20,}|chatgpt\.com/(?:c|share)/|"
    r'"(?:access_token|session_id|conversation_id)"\s*:', re.I
)


def check(root: Path, private_identifiers: tuple[str, ...] = ()) -> dict:
    root = root.resolve()
    paper = root / "preprints" / PAPER
    manifest = json.loads((paper / "RELEASE_MANIFEST.json").read_text())
    checksum_file = paper / "SHA256SUMS"
    listed = set()
    for line in checksum_file.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = root / relative
        if path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError(f"Unsafe artifact path: {relative}")
        if any(part in {".lake", "__pycache__"} for part in Path(relative).parts):
            raise ValueError("Build cache listed as a release artifact")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Checksum mismatch: {relative}")
        listed.add(relative)
    contributed = [paper, root / "lean" / "StickKnots"]
    files = [p for directory in contributed for p in directory.rglob("*") if p.is_file()]
    files += list((root / "reasoning_traces").glob("stick-knot-counting.*"))
    build_extensions = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".synctex"}

    def generated(path: Path) -> bool:
        relative = path.relative_to(root)
        if any(part in {".lake", "__pycache__"} for part in relative.parts):
            return True
        if path.parent == paper / "build":
            return path.name == "knot_fewnomials.pdf" or path.suffix in build_extensions
        return path.parent == root / "reasoning_traces" and path.suffix in build_extensions

    files = [path for path in files if not generated(path)]
    actual = {p.relative_to(root).as_posix() for p in files if p != checksum_file}
    if listed != actual:
        raise ValueError(f"Artifact inventory mismatch: {sorted(listed ^ actual)}")
    links = 0
    for path in files:
        relative = path.relative_to(root)
        if ".lake" in relative.parts or path.is_symlink():
            raise ValueError(f"Build cache or symlink exported: {relative}")
        if path.suffix in {".md", ".tex", ".lean", ".py", ".json", ".toml", ".cff"}:
            body = path.read_text()
            if SENSITIVE.search(body):
                raise ValueError(f"Machine path or private export marker in {relative}")
            if path.parent == root / "reasoning_traces":
                normalized = unquote(body).replace(r"\_", "_").casefold()
                if any(term.casefold() in normalized for term in private_identifiers):
                    raise ValueError(f"Private account identifier in {relative}")
            if path.suffix == ".md":
                body = re.sub(r"```.*?```", "", body, flags=re.S)
                body = re.sub(r"`[^`]*`", "", body, flags=re.S)
                for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", body):
                    if "://" in target or target.startswith(("#", "mailto:")):
                        continue
                    target = target.split("#", 1)[0]
                    if not target:
                        continue
                    if not (path.parent / target).resolve().is_file():
                        raise ValueError(f"Broken relative link in {relative}: {target}")
                    links += 1
        if path.suffix == ".pdf":
            reader = PdfReader(path)
            text = "\n".join(p.extract_text() or "" for p in reader.pages)
            if SENSITIVE.search(text + str(reader.metadata)):
                raise ValueError(f"Machine path or private export marker in PDF {relative}")
            if path.parent == root / "reasoning_traces":
                normalized = unquote(text + str(reader.metadata)).casefold()
                if any(term.casefold() in normalized for term in private_identifiers):
                    raise ValueError(f"Private account identifier in PDF {relative}")
            if reader.attachments:
                raise ValueError(f"Unexpected PDF attachment: {relative}")
            for key in ("/CreationDate", "/ModDate"):
                date = (reader.metadata or {}).get(key, "")
                if date != "D:20261023000000Z":
                    raise ValueError(f"Unexpected PDF build date in {relative}: {key}")
            for page in reader.pages:
                for annotation in page.get("/Annots", []):
                    obj = annotation.get_object()
                    if SENSITIVE.search(str(obj)):
                        raise ValueError(f"Private annotation marker in {relative}")
                    if path.parent == root / "reasoning_traces":
                        normalized = unquote(str(obj)).casefold()
                        if any(term.casefold() in normalized for term in private_identifiers):
                            raise ValueError(f"Private account identifier in annotation: {relative}")
                    action = obj.get("/A", {})
                    if action and action.get("/S") not in {"/URI", "/GoTo"}:
                        raise ValueError(f"Unexpected PDF action in {relative}")
    header = (
        "/-\nDiscussions and model prompting: Alexander Kolpakov (UATX).\n\n"
        "Source: sashakolpakov/StickNumbers, commit\n"
        "1609e1b38204b85363a7d2ef9222386596c30a50.\n-/\n\n"
    )
    formal = root / "lean" / "StickKnots"
    lean_sources = [p for p in formal.rglob("*.lean") if ".lake" not in p.parts]
    for path in lean_sources:
        body = path.read_text()
        if not body.startswith(header):
            raise ValueError("Lean source is missing the discussion/model-prompting credit")
        original = "formal/" + path.relative_to(formal).as_posix()
        if hashlib.sha256(body[len(header):].encode()).hexdigest() != manifest["source_sha256"][original]:
            raise ValueError("Lean proof body differs from the recorded source")
    acknowledgment = (
        r"\thanks{This working paper was developed through discussions and model "
        r"prompting by \mbox{Alexander Kolpakov (UATX)}.}"
    )
    body = (paper / "build/knot_fewnomials.tex").read_text()
    if body.count(acknowledgment) != 1:
        raise ValueError("Manuscript discussion/model-prompting credit is missing or duplicated")
    original = body.replace(acknowledgment, "", 1)
    if hashlib.sha256(original.encode()).hexdigest() != manifest["source_sha256"]["manuscript/knot_fewnomials.tex"]:
        raise ValueError("Mathematical manuscript source differs from the recorded source")
    for path in [paper / "knot_fewnomials.pdf", root / "reasoning_traces/stick-knot-counting.pdf"]:
        extracted = " ".join(" ".join(p.extract_text() or "" for p in PdfReader(path).pages).split())
        if "AlexanderKolpakov(UATX)" not in re.sub(r"\s+", "", extracted):
            raise ValueError("PDF is missing the discussion/model-prompting credit")
    return {"artifacts": len(actual), "relative_links": links,
            "source_revision": manifest["source_revision"],
            "private_identifier_count": len(private_identifiers), "status": "pass"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="Root of the prepared math tree")
    parser.add_argument("--private-identifiers-file", type=Path)
    args = parser.parse_args()
    private = ()
    if args.private_identifiers_file:
        private = tuple(line.strip() for line in args.private_identifiers_file.read_text().splitlines()
                        if line.strip() and not line.startswith("#"))
    print(json.dumps(check(args.root, private), indent=2))


if __name__ == "__main__":
    main()
