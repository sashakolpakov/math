# Contribution structure, provenance, and privacy audit

Audit date: 23 October 2026. Upstream reference:
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
The starting contribution was `d0e5ddb`.

The source checkout and the public source repository's main branch were
both verified at `2dc96272295b99c4932e8f71c9973deeef26581f`.
This audit covers the contribution's artifacts and claims. It does not
establish an independent mathematical proof review.

## Comparison with upstream

| Area | Observed upstream convention | Contribution treatment |
|---|---|---|
| Manuscript | A dated directory under `preprints/`, a PDF, build sources, and a manuscript README with citation information. | One manuscript directory containing the focused paper, its sources, bibliography, citation, build instructions, and hashes. |
| Reasoning material | The README describes abridged reasoning summaries for 10 selected families. The directory contains 10 PDFs and one TeX source. The two inspected examples include original-prompt and selected-reasoning excerpts. | One supporting PDF with TeX source and a coverage/privacy statement under `reasoning_traces/`. It is explicitly a retrospective research-development summary based on project records. |
| Contribution policy | No `CONTRIBUTING.md`, `AGENTS.md`, or `CODEOWNERS` file was found in the inspected upstream tree. | Observed conventions are distinguished from contribution requirements. No claim is made that a complete transcript is mandatory or that the package has been accepted. |
| Attribution | Upstream describes its own internal-model collection and uses OpenAI attribution. | The contribution is marked external and model-assisted; Alexander Kolpakov (UATX) and Nikolay Bogachev (University of Toronto) are credited for discussions and prompting. |
| Lean | The main library uses Lean 4.34.1; the formalization catalogue describes papers with formalized main results. Comparator configurations specify their checking targets. | The supporting package retains its known Lean 4.32.2/Mathlib pins and its separate build. It checks selected identities and conditional deductions, with no Comparator configuration or full main-theorem claim. |
| Collection indexing | Internal-model results have family identifiers and collection totals. | The manuscript and summary are linked in the external-contribution section. Existing family identifiers, totals, overview, and release history are preserved. |

Upstream also provides Comparator configurations for selected supporting
results. This contribution has not been ported into that build or supplied
with a Comparator target. The standalone package and its conditional scope
remain an explicit integration difference for maintainer review.

## Source-record coverage

The local source tree was inventoried, including ignored non-build files,
while dependency caches and generated build output were excluded. It
contains research notes, a provenance/influence ledger, manuscript audit
records, sources, and verification documentation. No original model
conversation export was found there.

The summary's provenance identifies its source revision and record types.
The public PDF presents a schematic research brief and mathematical outline.
It does not fabricate original
prompts, message sequences, verbatim model reasoning, model names, compute
statistics, or an independently authenticated chronology. The audit log's
references to review passes are reported as project records and are not
presented as independently established human peer review.

Raw-export anonymization remains outside the verified coverage because
those records were not available. The summary is publishable without
claiming that an unavailable archive has been redacted or authenticated.

## Privacy boundary

New and changed contribution text is checked for credentials, email
addresses, local paths, account/session export fields, and conversation
links. The summary's source, PDF text, metadata, and annotation targets are
also checked against a private identifier list kept outside the repository.
Matched values are never printed by the checker.

The requested contributor names and affiliations remain public. Existing
source-repository URLs and Git authorship identify public accounts; the
fork itself identifies its owner. Account-metadata omission in the summary
therefore does not imply anonymity of the entire project.

The PDF checks include document metadata, extracted text, XMP metadata,
annotation targets, attachments, and active/external-file actions. They
check for fixed UTC build dates. This is a bounded artifact audit, not a
guarantee against every possible form of hidden data in arbitrary exports.

## Concrete repair: build-clock configuration

The initial build command changed into the build directory after Latexmk's
initial configuration discovery, so it did not explicitly load the adjacent
fixed-clock configuration. The published PDF retained the local build time
despite the README's reproducibility claim.

The documented command now loads `build/.latexmkrc` explicitly. The
manuscript was rebuilt with the fixed epoch. Its 31 pages retain identical
extracted text; the metadata dates are now fixed UTC values. The summary
has its own explicitly selected clock configuration. Each PDF is checked
against two isolated clean builds with freshly copied source files.
These byte comparisons use the installed TeX toolchain: Latexmk 4.87 and
pdfTeX 1.40.29 from TeX Live 2026. They do not claim identical PDF bytes
across different TeX distributions or versions.

## Verification

The release checker verifies the single-manuscript scope, privacy checks,
local Markdown links, and artifact checksums. Its regression checks cover
credentials, account fields, private identifiers, local paths, hidden PDF
metadata, attachments, fixed dates, and a filename false-positive case.

The existing Lean source and proof bodies are unchanged by this audit.
The prior successful package build and axiom audit remain documented in
the Lean verification report. The manuscript's citations and final TeX
logs are checked separately. The development summary remains supporting
material for this one paper; no other manuscript has been reintroduced.

Results for this candidate: 43 added or changed paths passed the artifact
checker; all five privacy regression checks passed; the 31-page manuscript
and the two-page summary each matched two isolated rebuilds. Final TeX
logs had no unresolved citations/references, duplicate labels, missing
glyphs, hyperref warnings, or overfull boxes. Both summary pages were
visually inspected.

## Public summary editorial review

The public PDF was shortened to two pages. It presents an explicitly
schematic research brief, five development stages, the central mathematical
mechanism, and the scope of the Lean checks. Internal working-file
inventories, detailed repair histories, and operational discussion were
removed from that presentation. It includes no prompt quotations or chat
turns. The account-identifier check covers the known account handle,
local account name, public Git account email, and account number, with
the private values kept outside the repository. The named contributor
credits remain intentional.

## Repeating the checks

Create a Python environment and install the small audit dependency:

```sh
python3 -m pip install -r audit/requirements.txt
python3 audit/check_release.py --self-test
python3 audit/check_release.py --rebuild
```

Run these commands from this manuscript directory. A reviewer may also pass
`--private-identifiers-file /path/to/private-list` with one account handle or
other identifier per line. Keep that file outside the repository. The
checker reports counts and categories, without recording the identifiers
in public artifacts. Dependencies and generated build files are excluded
from the published artifact set.
