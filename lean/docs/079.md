# Local smoothing for the Euclidean wave equation

The following describes the scope of the Lean formalization related to the following accompanying paper(s):

- [Local smoothing for the Euclidean wave equation](../../preprints/Local-smoothing-for-the-Euclidean-wave-equation-October-25-2026/paper.pdf)
- [Critical local smoothing for the three-dimensional wave equation](../../preprints/Critical-local-smoothing-for-the-three-dimensional-wave-equation-September-24-2026/paper.pdf)

## Scope

For every dimension $n\ge 2$ and every $2\le p<\infty$, the formalization bounds the $L^p(\mathbb R^n\times[1,2])$ norm of the Euclidean half-wave by a constant times the $W^{s,p}(\mathbb R^n)$ norm of its Schwartz initial data. The Sobolev order is $s=\max(0,(n-1)/2-n/p)+\varepsilon$ for every $\varepsilon>0$, and $s=0$ is allowed at $p=2$. In dimension three this gives the critical $L^3$ estimate with arbitrarily small positive Sobolev loss.

The formalization also gives uniform Bochner–Riesz multiplier bounds, spherical extension estimates, and Stein square-function bounds in their strict ranges. The Kakeya maximal operator satisfies an $L^n$ bound with loss $\delta^{-\varepsilon}$ for every $\varepsilon>0$ at tube radii $0<\delta\le 1$. Every subset of $\mathbb R^n$ containing a unit segment in each direction has Hausdorff dimension $n$.

The development also proves a logarithmic lower bound for the volume occupied by tubes. In dimension three, at least $\delta^{-2}$ unit-length tubes of radius $\delta$ with $\delta$-separated directions have union volume at least $c/(1+\log(1/\delta))^{66}$, uniformly over their centers and $0<\delta\le 1$.

## Comparator links

| Result | Comparator statement |
| --- | --- |
| Euclidean half-wave local smoothing | [LocalSmoothing.lean](../ComparatorChallenges/LocalSmoothing.lean#L84) |
| Bochner–Riesz multiplier bounds uniform in the radius | [LocalSmoothing.lean](../ComparatorChallenges/LocalSmoothing.lean#L99) |
| Spherical restriction in extension form | [LocalSmoothing.lean](../ComparatorChallenges/LocalSmoothing.lean#L109) |
| Kakeya maximal estimate | [LocalSmoothing.lean](../ComparatorChallenges/LocalSmoothing.lean#L120) |
| Full Hausdorff dimension of Euclidean Kakeya sets | [LocalSmoothing.lean](../ComparatorChallenges/LocalSmoothing.lean#L129) |
| Stein square-function estimate | [LocalSmoothing.lean](../ComparatorChallenges/LocalSmoothing.lean#L134) |
