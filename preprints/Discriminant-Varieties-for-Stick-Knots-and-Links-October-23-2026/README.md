# [Discriminant Varieties for Stick Knots and Links](knot_fewnomials.pdf)

**Authors:** Alexander Kolpakov and Igor Rivin.

**Manuscript and contribution date:** October 23, 2026.

The manuscript presents quantitative bounds for the number of ordinary knot
types realizable with at most N sticks:

$$
N^{(2/3+o(1))N} \leq |\mathcal K_N| \leq N^{3N+o(N)},
\qquad \log |\mathcal K_N|=\Theta(N\log N).
$$

The authors describe this as, to their knowledge, the first explicit
determination of the logarithmic growth order by stick budget. The upper
bound uses direct real-algebraic discriminant chamber counting; a Garside
and arc-index construction supplies the lower bound. The result determines
the logarithmic growth order, without determining a leading asymptotic constant.
This external contribution is presented for mathematical review.

The [TeX source](build/knot_fewnomials.tex) contains its bibliography.
This is the revised repository manuscript dated October 23, 2026, and differs
from [arXiv v1](https://arxiv.org/abs/2608.01277v1).
The existing [model-assistance acknowledgment](ACKNOWLEDGMENTS.md) and both
human authors are preserved.

The [standalone Lean package](../../lean/StickKnots/README.md) verifies the
principal internal finite and asymptotic deductions from explicit external
theorem inputs. The [manuscript map](../../lean/StickKnots/MANUSCRIPT_MAP.md)
describes the boundary. It retains Lean 4.32.0 and its exact dependency pins;
it is built separately from the parent library and has no Comparator target.

The [public development summary](../../reasoning_traces/stick-knot-counting.pdf)
gives a schematic research brief and mathematical outline. Its
[source and privacy statement](../../reasoning_traces/stick-knot-counting.md)
distinguishes that retrospective account from an original conversation export.
[Mathematical](MATHEMATICAL_AUDIT.md) and [contribution](CONTRIBUTION_AUDIT.md)
audits accompany the package.

## Citation

```bibtex
@misc{kolpakov_rivin_stick_knots_2026,
  author = {Alexander Kolpakov and Igor Rivin},
  title = {Discriminant Varieties for Stick Knots and Links},
  year = {2026},
  eprint = {2608.01277},
  archivePrefix = {arXiv},
  note = {Repository revision dated October 23, 2026; differs from arXiv v1},
  url = {https://github.com/sashakolpakov/StickNumbers}
}
```

## Build and verify

From this preprint directory:

```sh
latexmk -r build/.latexmkrc -cd -pdf -interaction=nonstopmode -halt-on-error build/knot_fewnomials.tex
cp build/knot_fewnomials.pdf knot_fewnomials.pdf
python3 -m pip install -r audit/requirements.txt
python3 audit/check_release.py ../..
python3 audit/fewnomial_bound_audit.py --check-doubly-alternating 50 100 500 2000 10000
```

From the standalone Lean package directory, run:

```sh
lake exe cache get
make verify
```

[Provenance](PROVENANCE.md), RELEASE_MANIFEST.json and SHA256SUMS identify the
clean source snapshot, export adaptations, validation and artifact hashes.
The PDF clock is fixed; byte-for-byte reproducibility is checked with the
recorded TeX toolchain.
