> Attribution update, 27 October 2026: the contributor supplied the discussion/model-prompting credit for Alexander Kolpakov (UATX). This export now adds that credit in the manuscript, Lean headers and documentation using the Sarnak wording; all mathematical content and existing manuscript authors are preserved. The historical audit below predates this credit.

> Export note: this is a source-project audit record. The candidate changes
> described below were subsequently committed in source revision
> `1609e1b38204b85363a7d2ef9222386596c30a50`. This contribution uses that clean snapshot;
> see [provenance](PROVENANCE.md) for the current export boundary.

# Contribution scope and provenance audit

Prepared 23 October 2026 against source revision
`ee6d8f8c5cb3c4ef9f154e1173a7d05ffe9452b6` plus the current audited changes.
The generated `RELEASE_MANIFEST.json` records the precise source-file hashes
and completed validation. `SHA256SUMS` covers the exported artifacts.

The local reference was the external arithmetic-trace contribution in a
checkout of `openai/math`. Its observed layout is an example, not a statement
of universal contribution requirements or acceptance criteria.

| Area | Treatment |
|---|---|
| Manuscript | One dated preprint directory with revised source, PDF, fixed-clock build configuration, citation, audits and artifact manifest. The export identifies its difference from public arXiv v1. |
| Lean | A standalone Lean 4.32.0/mathlib package, independent of the corpus parent toolchain. All internal principal knot-counting deductions, including the new optimized deficit, are checked relative to explicit external inputs. |
| Reasoning material | A two-page retrospective development summary with source and coverage statement. No original chat export was present, so no original prompts, turns, runtime or model-run identity are authenticated. |
| Attribution | Alexander Kolpakov and Igor Rivin remain manuscript authors. The existing GPT-5.6-sol acknowledgment is preserved as source-reported provenance. Human discussion/prompting roles are not invented from the other contribution's template. |
| Indexing | Proposed entries are marked external and model-assisted; collection totals, internal family identifiers and existing contributions are preserved. |
| Formalization catalogue | The package has its own build and no Comparator target in the parent library. It is not entered as an unconditional main-result formalization. |
| Licensing | The source project has no checked-in license grant. The candidate preserves authorship and does not fabricate an Apache or other grant. Maintainers must resolve any license terms required for inclusion. |
| Publication | This is a local preparation. Neither upstream acceptance nor a published PR is claimed. |

## Mathematical and formal coverage

The separate mathematical audit reviews the upper chamber argument,
permutation construction, pure-braid correction, knot transfer, asymptotic
budget, auxiliary link construction and priority comparison. Cited deep
results remain external. The current Lean certificate proves their internal
composition using typed objects and actual maps, rather than treating the
final number of knots as a free numerical assumption.

The new `ManuscriptArithmetic.lean` closes the former elementary arithmetic
interface and proves the upper coefficient 3. The source scan rejects
unfinished proofs, project axioms and native-decision shortcuts; the compiled
declaration audit permits only the documented standard Lean/mathlib axioms.
That axiom list does not remove the external theorem hypotheses.

The classical ambient-isotopy quotient, Stiefel normalization, positive
measure statement and auxiliary link production are outside the formal
target. The source contains older conditional numerical wrappers, identified
as auxiliary in the manuscript map; the principal target uses the actual
bounded-stick subtype.

## Export coverage

An allowlist selects the manuscript, Lean source and configuration, reproducibility
tools, audits and summary. The exported text is checked for local machine
paths, obvious credential/export markers and broken relative Markdown links;
PDF text and metadata are inspected with `pypdf`, including attachment and
annotation checks. Public author names and source links remain intentional.
This bounded check is not a claim of anonymity or a claim to have redacted an
unavailable raw conversation archive.

The fixed build clock is 23 October 2026 UTC. Each PDF is compared with two
isolated clean rebuilds using the installed TeX toolchain. Repeatability is
tested on that installation, not promised across different TeX versions.
The generated manifest records actual successful commands. The package is
checked again after copying, including every artifact hash and Markdown link.

To repeat the exported-tree audit from the preprint directory:

```sh
python3 -m pip install -r audit/requirements.txt
python3 audit/check_release.py ../..
```

## Integration into the corpus checkout

The export is based on the clean committed source revision recorded above.
The manuscript TeX and every Lean proof file were compared byte-for-byte
with that source snapshot. The author names and existing model-assistance
acknowledgment are preserved. Documentation paths and provenance were adapted;
the public summary was edited into a schematic research brief and mathematical
outline, without working-file inventories or detailed repair history.

The full source preparation command passed in this session: complete Lean
build, 12-source scan, 17 compiled declaration/axiom checks, finite arithmetic
audit, both source PDF builds, two isolated rebuilds per source PDF, and the
source export checker. The integrated PDFs were additionally compared with
freshly copied sources in isolated directories, so fresh timestamps and changed
absolute paths were exercised. This uses the installed TeX toolchain.

The integrated artifact checker excludes only known generated build output
and local dependency caches from the artifact inventory; it rejects any such
cache listed in the release checksum manifest. A private identifier list can
be passed with --private-identifiers-file and is never copied into the release.
The public summary is checked for account handles, account numbers, account
emails and local-machine identifiers in its source, PDF text and metadata.
The separate provenance retains intentional public source URLs and authorship.

The package remains a standalone conditional Lean certificate. It is outside
the parent library's default build, has no Comparator configuration, and is
not registered as an unconditional main-result formalization. No internal-model
family identifiers, collection counts, or upstream release history were changed.
