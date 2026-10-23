#!/usr/bin/env python3
"""Audit the contribution's scope, privacy, links, hashes, and PDF builds.

Diagnostics identify categories and locations, never the matched private
values. Private identifier lists stay outside the public repository.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from urllib.parse import unquote, urlsplit

from pypdf import PdfReader, PdfWriter
from pypdf.generic import IndirectObject


ROOT = Path(__file__).resolve().parents[3]
SLUG = "Trace-Sparsity-and-Arithmeticity-for-Compact-Hyperbolic-Surfaces-October-23-2026"
PAPER = ROOT / "preprints" / SLUG
FORMAL = ROOT / "lean" / "ArithmeticTraceRigidity"
SUMMARY = ROOT / "reasoning_traces"
STEM = "compact-trace-rigidity"
UPSTREAM = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
FIXED_DATES = {"D:20260922000000Z", "D:20260922000000+00'00'"}
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


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout


def scan_text(text: str, label: str, private_terms: tuple[str, ...] = ()) -> list[str]:
    problems = []
    for category, pattern in PATTERNS.items():
        match = pattern.search(text)
        if match:
            line = text.count("\n", 0, match.start()) + 1
            problems.append(f"{label}:{line}: potential {category}")
    normalized = text.replace(r"\_", "_").casefold()
    if any(term.casefold() in normalized for term in private_terms):
        problems.append(f"{label}: private identifier")
    return problems


def audit_pdf(path: Path, private_terms: tuple[str, ...] = ()) -> list[str]:
    reader = PdfReader(path)
    problems = scan_text(
        "\n".join(str(value) for value in (reader.metadata or {}).values()),
        path.name + " metadata",
        private_terms,
    )
    problems += scan_text(
        "\n".join(page.extract_text() or "" for page in reader.pages),
        path.name + " extracted text",
        private_terms,
    )
    for key in ["/CreationDate", "/ModDate"]:
        if (reader.metadata or {}).get(key) not in FIXED_DATES:
            problems.append(f"{path.name}: build date is not fixed UTC")
    if reader.attachments:
        problems.append(f"{path.name}: embedded attachment")
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
                "/JavaScript", "/Launch", "/SubmitForm", "/ImportData", "/GoToR"
            }:
                problems.append(f"{path.name}: active or external-file PDF action")
            if "/URI" in value:
                uri = str(value["/URI"])
                problems.extend(scan_text(uri, path.name + " annotation", private_terms))
                if urlsplit(uri).scheme not in {"http", "https"}:
                    problems.append(f"{path.name}: non-web annotation target")
            for key, child in value.items():
                if key != "/Parent":
                    visit(child)
        elif isinstance(value, (list, tuple)):
            for child in value:
                visit(child)

    visit(reader.trailer["/Root"])
    metadata = reader.trailer["/Root"].get("/Metadata")
    if metadata is not None:
        problems.extend(scan_text(
            metadata.get_object().get_data().decode("utf-8", errors="replace"),
            path.name + " XMP metadata", private_terms,
        ))
    return problems


def check_hashes(manifest: Path) -> None:
    for line in manifest.read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = (manifest.parent / name).resolve()
        if not path.is_relative_to(manifest.parent):
            raise ValueError("checksum path escapes artifact directory")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"checksum mismatch: {manifest.name}: {name}")


def check_rebuild(source: Path, config: Path, artifact: Path, bibliography: Path | None) -> None:
    expected = hashlib.sha256(artifact.read_bytes()).hexdigest()
    for _ in range(2):
        with tempfile.TemporaryDirectory(prefix="trace-rigidity-rebuild-") as tmp:
            directory = Path(tmp)
            shutil.copyfile(source, directory / source.name)
            shutil.copyfile(config, directory / ".latexmkrc")
            if bibliography is not None:
                shutil.copyfile(bibliography, directory / bibliography.name)
            result = subprocess.run(
                ["latexmk", "-r", ".latexmkrc", "-pdf", "-gg",
                 "-interaction=nonstopmode", "-halt-on-error", source.name],
                cwd=directory, capture_output=True,
            )
            if result.returncode:
                raise ValueError(f"isolated build failed: {source.name}")
            actual = hashlib.sha256((directory / artifact.name).read_bytes()).hexdigest()
            if actual != expected:
                raise ValueError(f"isolated PDF differs: {artifact.name}")
    print(f"Two isolated PDF rebuilds match: {artifact.relative_to(ROOT)}")


class PrivacyChecks(unittest.TestCase):
    def test_credential_and_identity_fields(self):
        self.assertTrue(scan_text("ghp_" + "z" * 36, "fixture"))
        self.assertTrue(scan_text("account_id" + ": synthetic", "fixture"))
        serialized = '{"title":"synthetic","' + "session_id" + '":123}'
        self.assertTrue(scan_text(serialized, "fixture"))

    def test_filenames_are_not_credentials(self):
        self.assertFalse(scan_text("disk-" + "maximal-operator-theorem-2026", "fixture"))

    def test_private_identifier_and_local_path(self):
        self.assertTrue(scan_text("a private-example label", "fixture", ("private-example",)))
        self.assertTrue(scan_text("/" + "Users" + "/example/document", "fixture"))

    def test_hidden_metadata_and_attachment(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "fixture.pdf"
            writer = PdfWriter()
            writer.add_blank_page(width=100, height=100)
            writer.add_metadata({"/Author": "person" + "@" + "example.test"})
            writer.add_attachment("notes.txt", b"synthetic")
            writer.write(path)
            problems = audit_pdf(path)
            self.assertTrue(any("email address" in p for p in problems))
            self.assertTrue(any("embedded attachment" in p for p in problems))

    def test_safe_fixed_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "fixture.pdf"
            writer = PdfWriter()
            writer.add_blank_page(width=100, height=100)
            writer.add_metadata({
                "/CreationDate": "D:20260922000000Z",
                "/ModDate": "D:20260922000000Z",
            })
            writer.write(path)
            self.assertFalse(audit_pdf(path))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default=UPSTREAM)
    parser.add_argument("--private-identifiers-file", type=Path)
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(PrivacyChecks)
        return 0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1
    private_terms = ()
    if args.private_identifiers_file:
        private_terms = tuple(
            line.strip() for line in args.private_identifiers_file.read_text().splitlines()
            if line.strip() and not line.startswith("#")
        )
    changed = set(git("diff", "--name-only", args.base).splitlines())
    changed.update(git("ls-files", "--others", "--exclude-standard").splitlines())
    allowed_roots = (f"preprints/{SLUG}/", "lean/ArithmeticTraceRigidity/")
    allowed_files = {"README.md", "CONTENTS.md", "lean/README.md", "reasoning_traces/.gitignore"}
    problems = []
    for name in sorted(changed):
        path = ROOT / name
        if not (name in allowed_files or name.startswith(allowed_roots)
                or name.startswith("reasoning_traces/" + STEM + ".")):
            problems.append(f"unexpected contribution path: {name}")
        if not path.is_file() or path.is_symlink():
            problems.append(f"missing file or unexpected symlink: {name}")
            continue
        if path.suffix == ".pdf":
            terms = private_terms if path.parent == SUMMARY else ()
            problems.extend(audit_pdf(path, terms))
        else:
            text = path.read_text()
            if name in allowed_files:
                diff = git("diff", "--unified=0", args.base, "--", name)
                text = "\n".join(line[1:] for line in diff.splitlines()
                                 if line.startswith("+") and not line.startswith("+++"))
            terms = private_terms if path.parent == SUMMARY else ()
            problems.extend(scan_text(text, name, terms))
            if path.suffix == ".md":
                for match in re.finditer(r"\[[^\]]*\]\(([^)\s]+)\)", text):
                    target = match.group(1)
                    parsed = urlsplit(target)
                    if parsed.scheme or not parsed.path:
                        continue
                    resolved = (path.parent / unquote(parsed.path)).resolve()
                    if not resolved.is_relative_to(ROOT):
                        problems.append(f"{name}: link escapes repository")
                    elif not resolved.exists() and resolved.relative_to(ROOT).as_posix() not in tracked:
                        problems.append(f"{name}: missing Markdown target")
    preprint_pdfs = [p for p in changed if p.startswith("preprints/") and p.endswith(".pdf")]
    preprint_tex = [p for p in changed if p.startswith("preprints/") and p.endswith(".tex")]
    if preprint_pdfs != [f"preprints/{SLUG}/{STEM}.pdf"]:
        problems.append("contribution must contain exactly the focused manuscript PDF")
    if preprint_tex != [f"preprints/{SLUG}/build/{STEM}.tex"]:
        problems.append("contribution must contain exactly the focused manuscript TeX")
    raw_extensions = (".jsonl", ".html", ".har", ".mhtml", ".zip", ".sqlite", ".db")
    if (any(p.endswith(raw_extensions) for p in changed)
            or any(p.endswith(".json") and p != "lean/ArithmeticTraceRigidity/lake-manifest.json"
                   for p in changed)):
        problems.append("raw conversation/export file is outside the publication scope")
    for path in [PAPER / (STEM + ".pdf"), SUMMARY / (STEM + ".pdf")]:
        extracted = " ".join(
            (page.extract_text() or "") for page in PdfReader(path).pages
        )
        extracted = " ".join(extracted.split())
        for credit in ["Alexander Kolpakov", "Nikolay Bogachev", "UATX", "University of Toronto"]:
            if credit not in extracted:
                problems.append(f"{path.name}: missing contributor credit")
    for manifest in [PAPER / "SHA256SUMS", SUMMARY / (STEM + ".sha256")]:
        check_hashes(manifest)
    if problems:
        print("\n".join(sorted(set(problems))))
        return 1
    print(f"Release scope, text/PDF privacy, links and hashes: passed ({len(changed)} changed files)")
    print(f"Private identifier list applied to summary artifacts: {len(private_terms)} entries")
    if args.rebuild:
        check_rebuild(
            PAPER / "build" / (STEM + ".tex"), PAPER / "build/.latexmkrc",
            PAPER / (STEM + ".pdf"), PAPER / "build/biblio.bib",
        )
        check_rebuild(
            SUMMARY / (STEM + ".tex"), SUMMARY / (STEM + ".latexmkrc"),
            SUMMARY / (STEM + ".pdf"), None,
        )
    return 0


if __name__ == "__main__":
    tracked = set(git("ls-files").splitlines())
    raise SystemExit(main())
