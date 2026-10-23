# Novelty audit for the stick-knot counting result

Initial audit: 2026-08-02. Corpus audit update: 2026-10-23.

## Result being audited

For

$$
\mathcal K_N=\{K:\mathrm{stick}(K)\le N\},
$$

the manuscript proves

$$
N^{(2/3+o(1))N}\le |\mathcal K_N|\le N^{3N+o(N)}.
$$

Consequently

$$
\log |\mathcal K_N|=\Theta(N\log N).
$$

The priority claim concerns an explicit counting theorem in the literature:

> To our knowledge, this is the first explicit determination of the
> asymptotic growth order of the number of knot types realizable with at
> most $N$ sticks: $\log|\mathcal K_N|=\Theta(N\log N)$.

The contributions and their dependencies are:

- The direct self-intersection-discriminant argument gives the new upper
  bound $N^{3N+o(N)}$ using only $O(N^2)$ cubic and quartic walls in $3N$
  coordinates.
- The upper and lower proofs do not use Gros--Ramirez Alfonsin's
  strong-geometry reconstruction theorem. Their paper proves reconstruction
  of polygonal knot type from enriched sign data and does not state or prove
  an asymptotic knot-counting bound by stick number.
- The comparison exponents $33$ and $6$ below are retrospective deductions
  made in this project by combining their reconstruction result with
  additional polynomial encodings and sign-pattern estimates. They are not
  previously published stick-counting theorems and do not establish priority
  for that counting result. The reconstruction theorem itself retains its
  attribution as related geometric work.
- The Garside/Malyutin--Stupakov construction gives the new explicit lower
  exponent $2/3$, already among prime satellite knots. Earlier printed
  arc-index results already implied a smaller positive factorial exponent.
- The bounds determine an asymptotic growth order, not an asymptotic
  equivalent and not a limit for $\log|\mathcal K_N|/(N\log N)$.

## Closest prior results checked

| Source | What it gives | Relation to the manuscript |
|---|---|---|
| Freedman--He--Wang, *Möbius energy of knots and unknots* (1994), <https://doi.org/10.2307/2946626> | Exponential growth in crossing number. With the $O(N^2)$ crossing bound for an $N$-stick polygon, this gives the coarse baseline $\exp(O(N^2))$. | A classical general upper bound exists. |
| Calvo, *Geometric knot spaces and polygonal isotopy* (2001), <https://arxiv.org/abs/math/9904037> | Models labeled $N$-gons in $\mathbb R^{3N}$ and describes nonincident-edge intersection loci as cubic semialgebraic pieces; components of the embedding locus are geometric knot types. | Direct geometric precursor. The new upper theorem quantitatively counts a deliberately enlarged low-degree wall complement; the discriminant encoding itself is not new. |
| Randell--Simon--Tokle, *Möbius transformations of polygons and partitions of 3-space* (2008), <https://arxiv.org/abs/math/0602466> | Theorem 7 proves an exponential lower bound by polygon length. | Direct prior counting result, but below the factorial scale. |
| Millett, *Physical knot theory* (2010 manuscript), <https://web.math.ucsb.edu/~millett/Preprints/MillettTriesteLectures.pdf> | Problem 5.2 asks how many knot types occur among equilateral $N$-gons and reports no useful edge-number estimate at that time. | Historical evidence only; the model is equilateral. |
| Malyutin--Stupakov, *On the number of knots with a given arc index* (2022), <https://www.pdmi.ras.ru/preprint/2022/22-07.html> | Theorem 1 gives at least $\lfloor(k+4)/11\rfloor!$ oriented prime knots of arc index at most $k$. Proposition 1 injects $PB_n$ into oriented prime satellite knots with arc index at most $n\max\{11,s+8\}-4$ for an $s$-factor input. | The printed theorem plus Huh--Oh already gives $N^{(2/33+o(1))N}$ stick-bounded knots. The new variable-length extraction raises the exponent to $2/3$. |
| Elrifai--Morton, *Algorithms for positive braids* (1994), <https://doi.org/10.1093/qmath/45.4.479> | Starting/finishing sets and uniqueness of left canonical form for positive braids. | External Garside input ensuring that the selected long words are distinct. |
| Huh--Oh, *An upper bound on stick numbers of knots* (2011), <https://doi.org/10.1142/S0218216511008966> | $\mathrm{stick}(K)\le \tfrac32(\alpha(K)-1)$ for nontrivial knots. | Converts the arc-index construction into a stick-number lower bound. |
| Gros--Ramirez Alfonsin, *Strong geometry: knots*, v3 (2025), <https://arxiv.org/abs/2504.00197v3> | Theorem 1 says isomorphic affine strong geometries of generic point configurations yield isotopic polygonal knots; the following corollary says the wedge matroid alone suffices. The paper does not state an asymptotic count of knot types by stick number. | Related geometric work, independent of the present proof. The counting estimates derived below are this project's additional deductions, not counting theorems attributed to their paper. |
| Cantarella--Rechnitzer--Schumacher--Shonkwiler, *New upper bounds for stick numbers* (2025), <https://arxiv.org/abs/2508.18263> | Computational upper bounds for individual stick numbers. | Does not count all types realizable with $N$ sticks. |
| Pollack--Roy, *On the number of cells defined by a set of polynomials* (1993) | Dimension-sensitive cell bounds retaining the essential $(sd/m)^m$ dependence. | Shows that the real-algebraic technology predates this manuscript. |
| Barone--Basu, *Refined bounds on the number of connected components of sign conditions on a variety* (2012), <https://arxiv.org/abs/1104.0636> | Explicit component bounds for realizable sign conditions. | External theorem used on the actual cubic/quartic wall family. |

## Optional retrospective strong-geometry comparison

This calculation is separate from the manuscript's proof and priority claim.
It explains how one can obtain another counting bound from the 2025
reconstruction theorem after additional work. It is not a result claimed in
that paper and is not an input to either of our bounds.

Homogenize each vertex to $v_i=(1,p_i)\in\mathbb R^4$. Its full wedge ground
set contains a normal to every ordered triple of the $v_i$, hence at most
$N^3$ normals. The rank-four wedge chirotope has at most $N^{12}$ sign slots.
Unit normalization can be removed without changing a sign. In the resulting
cofactor normal, one coordinate has degree $3$ and the other three have degree
at most $2$, so every four-normal determinant has degree at most $9$. With
$3N$ real variables, standard fixed-degree sign-pattern counting gives

$$
\left(C\frac{N^{12}}{N}\right)^{3N}
=N^{33N+o(N)}.
$$

The proof of their knot theorem uses much less data: $O(N^2)$ affine signs for
crossings, over/under information, and crossing signs, plus $O(N^3)$ witness
signs ordering crossings along projected edges. The witness determinants have
degree at most $6$. Counting just these sign queries gives

$$
\left(C\frac{N^3}{N}\right)^{3N}
=N^{6N+o(N)}.
$$

Their reconstruction theorem turns equality of these labeled data into equal
knot type. Generic perturbation within the open PL embedding locus covers all
stick-bounded knot types. This is a sign-pattern count, not a chamber count.
The new discriminant argument obtains $N^{3N+o(N)}$ by counting components of
a smaller $O(N^2)$ wall complement.

## Lower-bound audit

The new lower proof no longer needs RSK or alternating-permutation
asymptotics. For $n=4k$, four arbitrary permutations of $k$ letters give an
explicit injective family of doubly down--up permutations of size $(k!)^4$.
Lean checks the construction, both descent conditions, injectivity, and

$$
(4k)!\le 2^{9k}(k!)^4.
$$

Elrifai--Morton normal-form uniqueness makes every $q$-letter word distinct;
endpoint pigeonholing costs $(4k)!$; Malyutin--Stupakov and Huh--Oh transfer
the family to stick-bounded prime satellite knots; forgetting orientation
costs at most $2$. Optimizing $q\sim\log N$ gives the $2/3$ exponent. Focused
searches found no prior use of this explicit family and variable-length
Garside optimization in the stick-number counting problem.

## Formal-verification status

The Lean development is a complete conditional certificate of the principal
stick-knot deductions, not an unconditional formal proof of the external
literature or the auxiliary link construction. It uses actual polygon
configurations, multivariate wall polynomials, paths and connected components,
permutation words and endpoint fibers, plus supplied braid and knot interfaces
and their pure-braid and bounded-stick subtypes. From
typed semantic, Barone--Basu, Garside, Malyutin--Stupakov, and Huh--Oh
interfaces it derives the final finite inequalities. No free numerical
“number of chambers/braids/knots” is assumed. It then proves the headline
`Theta(N log N)` law and, by a fixed-word argument, the eventual lower bound
with every coefficient `c < 2/3`. The optimized finite parameters are also
checked. The corpus audit adds `ManuscriptArithmetic.lean`, which proves the
explicit `-(2/3)N log log N + O(N)` evaluation and inhabits its previously
separate arithmetic interface. It also derives every eventual upper
coefficient greater than 3. See `formal/MANUSCRIPT_MAP.md` for the boundary
and `corpus/MATHEMATICAL_AUDIT.md` for the current written audit and the
difference between the repository manuscript and public arXiv v1.

## Defensible announcement wording

Use:

> To our knowledge, we give the first explicit determination of the
> asymptotic growth order of the number of knot types realizable with at
> most $N$ sticks. We prove
> $N^{(2/3+o(1))N}\le |\mathcal K_N|\le N^{3N+o(N)}$ for knot types realizable
> with at most $N$ sticks, hence $\log|\mathcal K_N|=\Theta(N\log N)$.
> A direct cubic/quartic discriminant count gives the upper bound, and an
> explicit Garside construction gives the lower bound.

The word “first” refers to an explicit determination of the logarithmic
growth order in the literature. It does not claim that earlier mathematics
could not be developed into another proof. The attribution of Calvo's model,
the real-algebraic component theorem, and the cited lower-bound inputs is
preserved. The separate comparison above must not be presented as a
previously published stick-counting theorem or as a dependency of our proof.
