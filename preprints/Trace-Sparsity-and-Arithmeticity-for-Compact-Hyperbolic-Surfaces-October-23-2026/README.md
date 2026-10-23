# [Trace Sparsity and Arithmeticity for Compact Hyperbolic Surfaces](compact-trace-rigidity.pdf)

**Discussions and model prompting:** Alexander Kolpakov (UATX) and
Nikolay Bogachev (University of Toronto).

**Manuscript date:** October 8, 2026. **Contribution date:** October 23, 2026.

This model-assisted working paper proves arithmeticity for every cocompact
Fuchsian lattice whose signed trace-counting function has upper polynomial
growth exponent at most one. It implies the compact Sarnak bounded-clustering
and Schmutz linear-growth conjectures, including compact orbifolds.
The submission is presented for mathematical review.

The [TeX source](build/compact-trace-rigidity.tex) and its
[bibliography](build/biblio.bib) are included.

The [standalone Lean project](../../lean/ArithmeticTraceRigidity/README.md)
verifies selected identities and conditional deductions from explicit
hypotheses. Its [manuscript map](../../lean/ArithmeticTraceRigidity/MANUSCRIPT_MAP.md)
identifies what is checked. The full geometric arithmeticity proof is not
formalized in Lean.

## Citation

```bibtex
@misc{ArithmeticTraceRigidity:compact:2026,
  title = {Trace Sparsity and Arithmeticity for Compact Hyperbolic Surfaces},
  year = {2026},
  note = {Working paper. Discussions and model prompting: Alexander Kolpakov
          (UATX) and Nikolay Bogachev (University of Toronto)},
  url = {https://github.com/sashakolpakov/arithmetic-trace-rigidity}
}
```

## Build

From this manuscript directory, with TeX Live and Latexmk installed:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error build/compact-trace-rigidity.tex
cp build/compact-trace-rigidity.pdf compact-trace-rigidity.pdf
```

`build/.latexmkrc` fixes the PDF build clock. `SHA256SUMS` records the
contributed PDF, source, bibliography, and build configuration.
[Provenance](../../lean/ArithmeticTraceRigidity/PROVENANCE.md) identifies the
source revision and contribution-specific adaptations.
