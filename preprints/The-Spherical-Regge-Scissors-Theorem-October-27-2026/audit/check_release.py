#!/usr/bin/env python3
"""Check the focused contribution's inventory, source equivalence and privacy.

Optional private identifiers are read from a file outside the repository.
Diagnostics report categories and locations without echoing private values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

from pypdf import PdfReader
from pypdf.generic import IndirectObject


SLUG = "The-Spherical-Regge-Scissors-Theorem-October-27-2026"
STEM = "spherical-regge-scissors"
CREDIT = "Discussions and model prompting: Alexander Kolpakov (UATX)."
HEADER = (
    "/-\n" + CREDIT + "\n\n"
    "Source: sashakolpakov/spherical-regge-scissors, commit\n"
    "d40eb8990bcf1ba5525435f8517e9ba5c202b549.\n-/\n\n"
)
ACKNOWLEDGMENT = (
    r"\thanks{This working paper was developed through discussions and model "
    r"prompting by \mbox{Alexander Kolpakov (UATX)}}" + "\n\n"
)
PATTERNS = {
    "local path": re.compile(
        r"/(?:Users|home)/|/private/(?:tmp|var)/|[A-Za-z]:\\Users\\|\bfile:\x2f{2}"
    ),
    "credential": re.compile(
        r"(?<![A-Za-z0-9_])(?:gh[pousr]_[A-Za-z0-9]{30,}|"
        r"github_pat_[A-Za-z0-9_]{30,}|sk-[A-Za-z0-9_-]{24,}|"
        r"AKIA[A-Z0-9]{16}|-----BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY-----)"
    ),
    "email address": re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}"),
    "export identity field": re.compile(
        r'(?im)(?:^\s*|[{,]\s*)"?(?:account|account_id|conversation_id|session_id|'
        r'device_id|request_id|user_id|access_token|api_key|authorization)"?\s*[:=]'
    ),
    "conversation link": re.compile(
        r"https?://(?:chatgpt\.com|chat\.openai\.com|claude\.ai)/(?:c|share|chat)/"
    ),
}
GENERATED = {
    ".aux", ".bbl", ".blg", ".log", ".out", ".toc", ".fls", ".fdb_latexmk",
}


def scan(text: str, label: str, private: tuple[str, ...] = ()) -> None:
    for category, pattern in PATTERNS.items():
        if pattern.search(text):
            raise ValueError(f"{label}: potential {category}")
    normalized = unquote(text).replace(r"\_", "_").casefold()
    if any(term.casefold() in normalized for term in private):
        raise ValueError(f"{label}: private account identifier")


def check_pdf(path: Path, expected_date: str, private: tuple[str, ...]) -> int:
    reader = PdfReader(path)
    scan("\n".join(str(x) for x in (reader.metadata or {}).values()), path.name + " metadata", private)
    extracted = "\n".join(page.extract_text() or "" for page in reader.pages)
    scan(extracted, path.name + " text", private)
    if "Alexander Kolpakov (UATX)" not in " ".join(extracted.split()):
        raise ValueError(f"{path.name}: missing human credit")
    for key in ("/CreationDate", "/ModDate"):
        if (reader.metadata or {}).get(key) != expected_date:
            raise ValueError(f"{path.name}: unexpected PDF build date")
    if reader.attachments:
        raise ValueError(f"{path.name}: embedded attachment")
    seen = set()

    def visit(value: object) -> None:
        if isinstance(value, IndirectObject):
            identity = (value.idnum, value.generation)
            if identity in seen:
                return
            seen.add(identity)
            visit(value.get_object())
        elif isinstance(value, dict):
            if "/JS" in value or value.get("/S") in {
                "/JavaScript", "/Launch", "/SubmitForm", "/ImportData", "/GoToR",
            }:
                raise ValueError(f"{path.name}: active or external-file PDF action")
            if "/URI" in value:
                uri = str(value["/URI"])
                scan(uri, path.name + " annotation", private)
                if urlsplit(uri).scheme not in {"http", "https"}:
                    raise ValueError(f"{path.name}: non-web annotation target")
            for key, child in value.items():
                if key != "/Parent":
                    visit(child)
        elif isinstance(value, (list, tuple)):
            for child in value:
                visit(child)

    visit(reader.trailer["/Root"])
    metadata = reader.trailer["/Root"].get("/Metadata")
    if metadata is not None:
        scan(metadata.get_object().get_data().decode("utf-8", errors="replace"),
             path.name + " XMP metadata", private)
    return len(reader.pages)


def check(root: Path, private: tuple[str, ...] = ()) -> dict:
    root = root.resolve()
    paper = root / "preprints" / SLUG
    formal = root / "lean" / "SphericalReggeScissors"
    summary = root / "reasoning_traces"
    manifest = json.loads((paper / "RELEASE_MANIFEST.json").read_text())
    checksum_file = paper / "SHA256SUMS"
    listed = set()
    for line in checksum_file.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = root / relative
        if relative in listed or path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError("Duplicate or unsafe checksum path")
        if any(part in {".lake", "__pycache__"} for part in Path(relative).parts):
            raise ValueError("Build cache listed as a release artifact")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Checksum mismatch: {relative}")
        listed.add(relative)

    def generated(path: Path) -> bool:
        if any(part in {".lake", "__pycache__"} for part in path.relative_to(root).parts):
            return True
        if path.is_relative_to(paper / "build" / "paper"):
            return path.suffix in GENERATED or path.name.endswith(".synctex.gz") or path.name == STEM + ".pdf"
        return path.parent == summary and path.suffix in GENERATED

    candidates = [p for directory in (paper, formal) for p in directory.rglob("*")
                  if p.is_file() or p.is_symlink()]
    candidates += list(summary.glob(STEM + ".*"))
    files = [p for p in candidates if not generated(p) and p != checksum_file]
    actual = {p.relative_to(root).as_posix() for p in files}
    if actual != listed:
        raise ValueError(f"Artifact inventory mismatch: {sorted(actual ^ listed)}")
    links = 0
    pages = {}
    for path in files:
        relative = path.relative_to(root).as_posix()
        if path.is_symlink():
            raise ValueError(f"Unexpected symlink: {relative}")
        terms = private if path.parent == summary else ()
        if path.suffix == ".pdf":
            date = "D:20261027000000Z" if path.parent == summary else "D:20260927000000Z"
            pages[relative] = check_pdf(path, date, terms)
            continue
        body = path.read_text(encoding="utf-8")
        scan(body, relative, terms)
        if path.suffix == ".md":
            body = re.sub(r"```.*?```|~~~.*?~~~", "", body, flags=re.S)
            body = re.sub(r"`[^`]*`", "", body)
            for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", body):
                parsed = urlsplit(target)
                if parsed.scheme or not parsed.path:
                    continue
                resolved = (path.parent / unquote(parsed.path)).resolve()
                if not resolved.is_relative_to(root) or not resolved.exists():
                    raise ValueError(f"Broken relative link in {relative}")
                links += 1
    for artifact, info in manifest["source_equivalence"].items():
        data = (root / artifact).read_bytes()
        if info["adaptation"] == "lean_credit_header":
            if not data.startswith(HEADER.encode()):
                raise ValueError(f"Missing credit header: {artifact}")
            data = data[len(HEADER.encode()):]
        elif info["adaptation"] == "tex_acknowledgment":
            if data.count(ACKNOWLEDGMENT.encode()) != 1:
                raise ValueError("Missing or duplicated manuscript acknowledgment")
            data = data.replace(ACKNOWLEDGMENT.encode(), b"", 1)
            layout = b"\\enlargethispage{20pt}\n"
            if data.count(layout) != 1:
                raise ValueError("Missing first-page allowance for the acknowledgment")
            data = data.replace(layout, b"", 1)
        elif info["adaptation"] != "verbatim":
            raise ValueError("Unsupported source-equivalence adaptation")
        if hashlib.sha256(data).hexdigest() != info["sha256"]:
            raise ValueError(f"Mathematical source differs: {artifact}")
    if pages != manifest["pdf_pages"]:
        raise ValueError("PDF page counts differ from release manifest")
    return {"status": "pass", "artifacts": len(actual), "relative_links": links,
            "source_revision": manifest["source_revision"],
            "preserved_source_files": len(manifest["source_equivalence"]),
            "private_identifier_count": len(private)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="Root of the prepared math tree")
    parser.add_argument("--private-identifiers-file", type=Path)
    args = parser.parse_args()
    private = ()
    if args.private_identifiers_file:
        private = tuple(x.strip() for x in args.private_identifiers_file.read_text().splitlines()
                        if x.strip() and not x.startswith("#"))
    print(json.dumps(check(args.root, private), indent=2))


if __name__ == "__main__":
    main()
