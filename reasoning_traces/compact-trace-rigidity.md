# Research development summary: compact trace rigidity

[Read the abridged summary](compact-trace-rigidity.pdf) ·
[TeX source](compact-trace-rigidity.tex) ·
[Accompanying manuscript](../preprints/Trace-Sparsity-and-Arithmeticity-for-Compact-Hyperbolic-Surfaces-October-23-2026/README.md)

Discussions and model prompting: **Alexander Kolpakov (UATX)** and
**Nikolay Bogachev (University of Toronto)**.

## Source and scope

This is a retrospective summary of the development recorded in the source
project's provenance ledger, audit log, and mathematical notes. It covers
only *Trace Sparsity and Arithmeticity for Compact Hyperbolic Surfaces*.
It is an editorial account of those records. It contains no verbatim model
quotations or reconstructed chat turns.

The PDF gives a schematic research brief, the main stages of the mathematical
development, the resulting proof mechanism, and the scope of the Lean checks.
Its source revision is identified in the
[provenance document](../lean/ArithmeticTraceRigidity/PROVENANCE.md).
Source-coverage details are kept in the
[contribution audit](../preprints/Trace-Sparsity-and-Arithmeticity-for-Compact-Hyperbolic-Surfaces-October-23-2026/CONTRIBUTION_AUDIT.md).

No original conversation export was available in the audited project tree.
The research brief is an editorial description of the task, not an original
prompt quotation. Exact dialogue and model-run statistics are not
authenticated by this summary.

## Privacy boundary

The summary omits account handles, account identifiers, email addresses,
conversation and session identifiers, share links, local filesystem paths,
credentials, and export headers. The contributor names and affiliations
above are intentional public attribution.

The public PDF omits internal working-file names, detailed repair logs,
prompt recipes, and operational information. It retains the mathematical
problem, the strategic change, the proof outline, and verification scope.

Source-repository attribution and public Git authorship remain in the
contribution's provenance. The fork itself is public and identifies its
owner. This document makes no claim that the complete contribution is
anonymous. Raw conversation exports are not part of the publication.

## Build and audit

From this directory:

    latexmk -r compact-trace-rigidity.latexmkrc -pdf \
      -interaction=nonstopmode -halt-on-error compact-trace-rigidity.tex

The compact-trace-rigidity.sha256 file records the source, configuration,
documentation, and PDF hashes. The manuscript's
[contribution audit](../preprints/Trace-Sparsity-and-Arithmeticity-for-Compact-Hyperbolic-Surfaces-October-23-2026/CONTRIBUTION_AUDIT.md)
documents structure, privacy, and reproducibility checks.
