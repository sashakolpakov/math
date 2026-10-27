# [The Spherical Regge Scissors Theorem](spherical-regge-scissors.pdf)

*A Conditional Proof through an Explicit Weight-Two Contract*

**Discussions and model prompting:** Alexander Kolpakov (UATX).

**Manuscript date:** 27 September 2026. **Contribution date:** 27 October 2026.

This working paper proves a conditional implication: if the explicit
external theorem package E1–E8 is supplied for a nondegenerate spherical
tetrahedron and its elementary Regge mate, then the pair admits a finite
spherical equidecomposition. The relative motivic construction and
comparison bridge E2–E5 remains unresolved. The contribution does not
establish the unconditional spherical Regge scissors theorem.

The internal argument checks the Regge matrix and phase action, the Gram
determinant and rational orientation charts, four-channel tensor
cancellation, and the specialization and scissors-group deductions. The
[standalone Lean package](../../lean/SphericalReggeScissors/README.md)
checks that algebra and the implication from a supplied `ProofContract`.
Its [manuscript map](../../lean/SphericalReggeScissors/MANUSCRIPT_MAP.md)
and [status statement](STATUS.md) identify the mathematical boundary.

The [TeX driver](build/paper/spherical-regge-scissors.tex), five section
files, macro file and bibliography preserve the mathematical content of
the focused [source repository](https://github.com/sashakolpakov/spherical-regge-scissors).
This export adds the discussion/model-prompting acknowledgment above,
following the style of the Sarnak contribution. The source author field
remains blank; this credit describes a role rather than assigning authorship.

An abridged [development summary](../../reasoning_traces/spherical-regge-scissors.pdf)
gives a schematic research brief and mathematical route. Its
[source and privacy statement](../../reasoning_traces/spherical-regge-scissors.md)
distinguishes the retrospective account from an original conversation.
The [critical-path audit](CRITICAL_PATH_AUDIT.md) and
[self-containedness audit](SELF_CONTAINEDNESS_AUDIT.md) are included.

## Citation

```bibtex
@misc{spherical_regge_scissors_contract_2026,
  title = {The Spherical Regge Scissors Theorem:
           A Conditional Proof through an Explicit Weight-Two Contract},
  year = {2026},
  note = {Conditional working paper, 27 September 2026.
          Discussions and model prompting: Alexander Kolpakov (UATX)},
  url = {https://github.com/sashakolpakov/spherical-regge-scissors}
}
```

## Build and verify

From this preprint directory:

```sh
cd build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=paper paper/spherical-regge-scissors.tex
cp paper/spherical-regge-scissors.pdf ../spherical-regge-scissors.pdf
cd ..
python3 -m pip install -r audit/requirements.txt
python3 audit/check_bibliography.py
python3 audit/check_pdf_reproducibility.py
python3 audit/check_release.py ../..
```

From `lean/SphericalReggeScissors`, run `lake exe cache get` and `make verify`.
The project retains Lean 4.32.2 and its exact Mathlib pins, independently of
the parent library and without a parent Comparator target.

[Provenance](PROVENANCE.md), RELEASE_MANIFEST.json and SHA256SUMS record
the clean source snapshot, export adaptations, validation and hashes.
SOURCE_RELEASE_MANIFEST.md describes the historical source artifact;
the current checksum inventory describes the rebuilt, credited contribution.
