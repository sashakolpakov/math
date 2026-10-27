> Imported historical source manifest from `d40eb8990bcf1ba5525435f8517e9ba5c202b549`. Its PDF digest and unattributed status describe the original release. This contribution adds the requested discussion/model-prompting acknowledgment and rebuilds the PDF; current hashes and validation are in RELEASE_MANIFEST.json and SHA256SUMS.

# Pre-release candidate manifest

Candidate name: **Spherical Regge Scissors**<br>
Repository slug: `spherical-regge-scissors`<br>
Repository URL: <https://github.com/sashakolpakov/spherical-regge-scissors><br>
Documentation URL: <https://sashakolpakov.github.io/spherical-regge-scissors/><br>
Verification date: 27 September 2026 (Europe/Zurich)

This manifest describes the conditional-proof and Lean-formalization
pre-release candidate. No archival tag, journal acceptance, authorship
attribution, independent expert validation, or unconditional proof is
claimed. The checked theorem is the implication from the explicit E1--E8
contract; construction of E2--E5 for spherical tetrahedra remains external.

## Manuscript artifact

| Artifact | Pages | SHA-256 | Provenance |
|---|---:|---|---|
| `paper/spherical-regge-scissors.pdf` | 25 | `2fe8f84254a66cc861b1c0e3d26c2b74add3716c8c80b0899f4d93860d757517` | Reproducibly built from the adjacent TeX driver, five section files, macro file, and seven-entry bibliography; unattributed conditional research draft |

The repository fixes `SOURCE_DATE_EPOCH=1790467200`,
`FORCE_SOURCE_DATE=1`, and `TZ=UTC` through `.latexmkrc` and the root
Makefile.  The isolation check copies the TeX sources without preserving
modification times, rebuilds under a different absolute path, and requires
the resulting PDF digest to match the checked-in artifact byte for byte.

## Toolchain

- Latexmk 4.87
- pdfTeX 3.141592653-2.6-1.40.29 (TeX Live 2026/Homebrew)
- BibTeX 0.99e
- Ghostscript 10.07.0 for page-count verification
- Python 3.10 or later for the repository scripts; verified with Python 3.14.6
- ripgrep for final TeX/BibTeX log scans
- Sphinx 9.1.0 and Furo 2025.12.19 for the mathematical guide
- Lean 4.32.2, pinned by `formal/lean-toolchain`
- Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`, pinned by
  `formal/lake-manifest.json`

## Verification result

The command

```sh
make verify
```

completed successfully on this candidate.  It performs a forced manuscript build,
validates exact citation coverage, scans final TeX and BibTeX logs, checks
public-source hygiene and relative Markdown links, builds all Lean modules,
rejects proof placeholders and project axioms, audits the printed axioms of
22 public declarations, checks the 22-item manuscript-to-Lean coverage map
and the exhaustive 77-field E1--E8 contract map,
builds the Sphinx guide with warnings treated as errors, rebuilds the PDF in
an isolated temporary path, and checks the artifact set, page count, and
SHA-256 digest against this manifest.

The final pdfTeX log contains no font-expansion notice, undefined citation or
reference, duplicate label, missing glyph, overfull box, or underfull box
warning; the BibTeX log has no warning.

The same `make verify` target completed successfully both in a clean local
clone of the committed tree and in a fresh HTTPS clone of the public GitHub
repository, after reconstructing the pinned dependency tree and official
Mathlib cache.  The hosted Lean and Documentation workflows both succeeded;
the repository, deployed strict Sphinx guide, and Lean-formalization page were
then retrieved from their public URLs with HTTP 200 responses.
