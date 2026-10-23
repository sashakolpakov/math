# Contribution verification

Verification date: 23 October 2026.

`make verify` passed in this standalone project. It ran the comment-aware
source scan over all 12 project Lean files, built the package with the
pinned Lean 4.32.2 toolchain and Lake manifest, and compiled the public
entry point while auditing its printed axiom dependencies. Only
`Classical.choice`, `Quot.sound`, and `propext` occurred in that audit.
The build reused the source project's existing pinned dependency cache;
no dependency cache or build artifacts are included in the contribution.

Each imported Lean source was compared with source commit
`2dc96272295b99c4932e8f71c9973deeef26581f`: removing the new discussion and
prompting credit comment recovers the original source exactly.

The contributed manuscript was rebuilt with LaTeX and BibTeX. Its final
logs contain no unresolved citations or references, duplicate labels,
missing glyphs, hyperref warnings, or overfull boxes. All citation keys
resolve against the included source bibliography. Removing the added credit
footnote recovers the original TeX source exactly.

The credits and affiliations were checked in extracted PDF text, and the
title-page layout was visually inspected. The manuscript's `SHA256SUMS`
matches its contributed PDF, TeX source, bibliography, and build
configuration. The contributed relative Markdown links resolve, allowing
for upstream files omitted from the sparse checkout.

These are artifact, source-preservation, and Lean build checks. The
formalization's mathematical scope is described in the README and
manuscript map: it checks selected calculations and deductions from explicit
hypotheses, rather than the complete geometric arithmeticity proof.

## Structure and privacy audit

The [contribution audit](../../preprints/Trace-Sparsity-and-Arithmeticity-for-Compact-Hyperbolic-Surfaces-October-23-2026/CONTRIBUTION_AUDIT.md)
adds a retrospective development summary, an explicit source/privacy
boundary, and text/PDF release checks. The corrected manuscript build
command explicitly loads its fixed-clock configuration. The manuscript
and summary PDFs each matched two isolated clean rebuilds using the
recorded TeX toolchain. The manuscript retains identical extracted text
on all 31 pages, and the Lean source files were not changed by this audit.
