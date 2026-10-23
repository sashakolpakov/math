> Export note: this is a source-project audit record. The candidate changes
> described below were subsequently committed in source revision
> `1609e1b38204b85363a7d2ef9222386596c30a50`. This contribution uses that clean snapshot;
> see [provenance](PROVENANCE.md) for the current export boundary.

# Mathematical audit for the corpus candidate

Audit date: 23 October 2026. Starting source revision:
`ee6d8f8c5cb3c4ef9f154e1173a7d05ffe9452b6`.
The candidate includes the uncommitted, explicitly inventoried changes made
during this audit. The export records per-file hashes, rather than describing
the candidate as identical to that starting commit.

## Result and priority

For ordinary unoriented knot types of stick number at most `N`, the manuscript
establishes

\[
N^{(2/3+o(1))N}\le |\mathcal K_N|\le N^{3N+o(N)}.
\]

This is matching order for the logarithm, `log |K_N| = Θ(N log N)`.
It is not a constant-factor tight estimate for `|K_N|`, an asymptotic
equivalent, or a proof that the normalized logarithm has a limit.

The supported priority wording is: “To our knowledge, this is the first
explicit determination of the asymptotic growth order of the number of knot
types realizable with at most `N` sticks.” The qualification “logarithmic
growth order” specifies exactly what is tight.

Gros–Ramírez Alfonsín's 2025 paper proves a reconstruction theorem and does
not state an asymptotic stick-counting theorem. Neither of our bounds uses
it. The comparison exponents 33 and 6 in `NOVELTY_AUDIT.md` are additional
retrospective deductions made in this project, not previously published
stick-counting results. They do not displace priority for the explicit
counting theorem. A brief related-work citation remains in the manuscript.
The separate 2022 arc-index theorem and 2011 arc-to-stick inequality supply
the earlier lower-bound inputs, and the new Garside extraction gives 2/3.
As usual, “to our knowledge” refers to the literature checked.

The [public arXiv v1](https://arxiv.org/abs/2608.01277v1) has an older abstract
and an older affine-slice argument. This contribution exports the audited
repository manuscript, dated 23 October 2026, and does not claim byte identity
with arXiv v1. Updating arXiv is a separate publication action.

## Main proof audit

| Step | Mathematical check | Outcome |
|---|---|---|
| Normalization | Centering gives row vectors in `1⊥`; the positive-definite square root normalizes the Gram matrix by an orientation-preserving linear map. The Stiefel and oriented Grassmannian dimensions are `3N−9` and `3N−12`. Connected `SO(3)` fibers preserve component counts. | Consistent; not needed for the unsliced upper estimate. |
| Support | Subdivision reaches exactly `N` vertices. PL stability permits a full-dimensional generic perturbation without changing knot type. The relevant wall polynomials are nonzero polynomials for `N≥4`. | Every bounded-stick type has a wall-free representative. Straight subdivision vertices must be perturbed before imposing the adjacent walls. |
| Walls | Nonincident intersection forces the cubic scalar triple product to vanish. A nonzero squared cross product excludes collapsed edges and adjacent overlap. Redundant ordered slots and constant-one slots do not change the nonzero locus. | Correct necessary walls; their signs alone are not asserted to classify knots. |
| Topology | Paths of fixed-combinatorics embeddings preserve ambient isotopy; an open Euclidean locus is locally path connected. The classifier is surjective on the actual bounded-stick subtype. | Knot count is at most the number of components. A lower chamber count alone would not give a knot lower bound. |
| Component count | Barone–Basu Theorem 1.1 with ambient and variety dimension `3N` and fixed degree four gives a fixed exponential factor times the weighted partial binomial sum. Duplicated slots only enlarge the bound. | The dimension dependence retains the crucial factorial denominator. |
| Entropy saving | For `S=N+N²`, `m=3N` and `N≥5`, `m≤(S+1)/2`. Bound the sum by `(m+1)4^m choose(S+1,m)` and use the factorial denominator. | Base `O(N)` in exponent `3N`; the fixed factor and prefactor give only `O(N)` logarithmic error. |
| Permutations | The four permutations map `(h,r,p)` to `(1−p,σ[h,p](r),1−h)`. Both the permutation and inverse have the required descent pattern. The four inputs are recoverable. | At least `(k!)⁴` letters and factorial deficit at most `9k log 2`. |
| Long words | Equal starting/finishing sets make each word a left normal form. Endpoint pigeonholing costs `(4k)!`. Appending one common inverse-endpoint simple braid preserves distinctness by cancellation. | At least `ceil(g[4k]^q/(4k)!)` short pure braids. |
| Knot transfer | The cited pure-braid injection preserves distinct oriented classes, produces prime satellites, and has the stated `n max(11,s+8)−4` arc budget. Orientation forgetting has fibers at most two. Huh–Oh applies because satellites are nontrivial. | Finite lower bound, factor-two loss, and stick cutoff agree. |
| Fixed words | `k=floor(N/(6(q+9)))` is positive eventually, fits the budget, and gives coefficient `2(q−1)/(3(q+9))`. Let fixed `q` increase after choosing a desired coefficient. | Every `c<2/3` is eventually a valid lower coefficient. The manuscript now states the eventual positivity explicitly. |
| Varying words | `q=floor(log N)`, `k=floor((2N+15)/(12(q+9)))`. Capacity and remainder control floor losses; `log² N=o(N)` absorbs the remaining errors. | The new Lean module proves the explicit `−(2/3)N log log N−O(N)` lower deficit, closing the previous arithmetic interface. |

## Auxiliary links

For each fixed component decomposition the wall argument works in `3N`
coordinates. At most `N!` decompositions suffice, giving the stated (possibly
nonoptimal) upper exponent 4.

For the addressed linking construction, the parity graph identifies `R`
by its two leaf neighbors when `m≥2`, then identifies `F₁`, the remaining
frame path, and each payload leaf successively. Only the two unused leaves
can be interchanged. Thus the absolute linking matrix recovers all payload
entries despite forgetting component labels and orientations.

The written routing proof is strengthened in this candidate: rail points lie
on a circle, return rails lie on the doubled circle, and the initial radial
rectangles form an unlink. A thin prism along a selected chord misses every
other rail and every return rail. An affine copy of a fixed polygonal full
twist has constant stick cost, independent of the pair and the number of
rails. Separate slabs prevent interactions between operations. Hence the
cost is `O(m+sum a_ij)`. Stars and bars gives `choose(choose(n,2)+n,n)`.
This auxiliary link argument is reviewed on paper, not formalized in Lean.
The factorial lower scale for links also follows directly from the knot
subclass, independently of this construction.

## Checked literature interfaces

* [Barone–Basu, Theorem 1.1](https://arxiv.org/pdf/1104.0636): the explicit
  binomial component estimate, including ambient-dimension factors.
* [Elrifai–Morton, Algorithms for positive braids](https://www.liverpool.ac.uk/~su14/papers/elrifaimorton.pdf):
  canonical form and starting/finishing criteria. Interchanging descent
  conventions has no effect because both sets in the chosen family coincide.
* [Malyutin–Stupakov, preprint 07/2022](https://www.pdmi.ras.ru/preprint/2022/22-07.html),
  Theorem 1 and Proposition 1, printed pages 3–4: the original Russian PDF
  was retrieved and its injection, prime/satellite properties, and factor
  budget checked. The indexing bounds used here stay within its range.
* [Huh–Oh, Theorem 3](https://arxiv.org/pdf/1512.03592): the precise inequality
  `stick(K)≤(3/2)(arc(K)−1)` for nontrivial knots.
* [Gros–Ramírez Alfonsín, v3, Section 4.3](https://arxiv.org/html/2504.00197v3):
  related reconstruction theorem, unused by the counting proof. The separate
  counting comparison in the novelty audit is a deduction made here.

The audit checks the cited statements and how they are applied; it does not
re-prove these papers or represent independent human peer review. The
declaration-level formal boundary is in the accompanying manuscript map.
