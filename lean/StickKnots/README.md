# Lean certification boundary

**Discussions and model prompting:** Alexander Kolpakov (UATX).

This directory contains the Lean 4.32/mathlib certification accompanying
`../../preprints/Discriminant-Varieties-for-Stick-Knots-and-Links-October-23-2026/build/knot_fewnomials.tex`.  It has no `sorry`, `admit`,
`native_decide`, or project-specific `axiom` declarations.

The right description is **complete conditional certification of the
principal stick-knot deductions**, not a complete formal proof of the cited
literature or of every auxiliary link construction.  Deep inputs such as
Barone--Basu, ambient-isotopy extension, Garside normal-form uniqueness,
Malyutin--Stupakov, and Huh--Oh are passed as typed theorem hypotheses.  Lean
then checks the actual polygonal objects, the supplied braid and knot
interfaces, and every deduction from those interfaces to
the stated finite/asymptotic bounds, probability formulas, or decision results.  In particular, the principal
certificates no longer quantify over unexplained numerical “numbers of
chambers,” “numbers of braids,” or “numbers of knots.”

Build and audit the complete target with:

```sh
lake exe cache get
make verify
```

`StickKnots.lean` imports every module and runs `#print axioms` on the main
declarations.  The expected dependencies are only Lean/mathlib foundations,
not assumptions declared by this project.  The external mathematical inputs
are ordinary theorem parameters, so `#print axioms` audits the conditional
deductions rather than proving those inputs.

## Stick-number upper certificate

The following chain is checked on actual typed objects.

- `PolygonalCore.lean` defines an `N`-vertex configuration, its cyclic edge
  paths and finite segment sets, the cubic nonincident-edge determinant walls,
  and the quartic adjacent-edge cross-product walls.
- The walls are genuine `MvPolynomial (Fin N × Fin 3) ℝ` values.  Lean proves
  their evaluation identities and degree bounds, and proves that avoiding all
  indexed walls implies the finite-edge embedding conditions.
- Lean proves that the geometric wall-free locus is exactly the simultaneous
  nonzero locus of those polynomials, that this locus is open and locally path
  connected, and that its connected-component and path-component types agree.
- `CertificationLogic.lean` uses mathlib's `Path`, `ZerothHomotopy`, and
  `ConnectedComponents`.  A classifier constant on genuine paths factors
  through path components; surjectivity then gives the cardinal inequality.
- `StickUpperCertificate.lean` defines the bounded-stick subtype
  `{K // stickNumber K ≤ N}` of the supplied knot carrier and transports
  components through a homeomorphism
  between polygon coordinates and polynomial coordinates.
- The real-algebraic boundary is the theorem-shaped interface
  `DegreeFourComponentTheorem factor`: for every finite family of real
  polynomials of degree at most four, it supplies the stated component bound.
  It is not a knot-specific or conclusion-shaped count assumption.
- From that interface and the typed knot classifier/support certificate, Lean
  proves

  ```text
  boundedStickKnot_count_le_unsliced:
    Nat.card {K // stickNumber K ≤ N}
      ≤ (3N+1) (12·factor·N)^(3N)        (N ≥ 5),
  ```

  with the displayed inequality stated over `ℝ`.  The factorial-sensitive
  binomial estimate producing the linear base is proved in mathlib arithmetic.

What remains external is precisely the topology/support input: that every
bounded-stick knot has a generic wall-free representative and that a path of
wall-free polygonal embeddings preserves ambient-isotopy class.  The
Barone--Basu component theorem is also external.  The development does not
construct a quotient type of PL embeddings by ambient isotopy; instead it
accepts the resulting classifier theorem on the actual polygon space.

## Stick-number lower certificate

The lower chain is likewise typed rather than numerical.

- `DoublyAlternating.lean` defines doubly down--up permutations and gives an
  explicit injection from four independent permutations of `Fin k`.  Lean
  checks both descent conditions, injectivity, and
  `(k!)^4 ≤ |G_{4k}|`.
- It proves `(4k)! ≤ 2^(9k)(k!)^4` and the corresponding `O(k)` logarithmic
  deficit.  No RSK correspondence or Euler-number asymptotic is needed.
- `LowerCertification.lean` defines the actual word type
  `Fin q → DoublyDownUpPerm (4k)`, its endpoint fibers, and the subtype of pure
  braids with trivial endpoint.  From structural Garside data, Lean performs
  endpoint pigeonholing, appends the inverse endpoint, proves purity and
  injectivity by right cancellation, and proves the `q+1` factor-length bound.
- The Malyutin--Stupakov map, arc index, orientation-forgetting map, stick
  number, and bounded prime-satellite knot family are actual functions and
  subtypes in the certificate.  Lean composes their injectivity and budget
  statements, derives the factor-two loss from the reversal description of an
  unoriented knot, and proves

  ```text
  finite_stick_lower_bound:
    ((k!)^4)^q
      ≤ 2·(4k)!·Nat.card(bounded prime-satellite knot types).
  ```

The structural facts supplied externally are the interpretation of the
abstract braid carrier as the classical Artin braid group, Elrifai--Morton
normal-form uniqueness/right cancellation/length facts,
Malyutin--Stupakov's injective braid-to-knot construction and arc estimate,
and Huh--Oh's stick/arc inequality.  Lean
does not merely assume the endpoint loss or the final lower count: it derives
them from those typed maps.

In the end-to-end theorem, finiteness of the bounded prime-satellite target is
not an external lower-side field.  Lean first obtains finiteness of the full
bounded-stick subtype from the upper semantic/component certificate, then
pulls it back along the actual injection from the lower family.

## End-to-end asymptotic certificate

`AsymptoticCertificate.lean` connects both finite arguments on the concrete
subtype `BoundedStickKnot stickNumber N` of the supplied knot carrier; there is
no free numerical variable standing for the number of knots.

- It proves the exact optimized finite lower inequality for
  `q = floor(log N)` and
  `k = floor((2N+15)/(12(q+9)))`, including the stick budget and a
  factorial-free lower envelope obtained from mathlib's global Stirling bound.
- Independently of that optimization, it uses `q = 2` and
  `k = floor(N/132)` to prove the headline theorem

  ```text
  certifiedKnotCount_log_isTheta:
    (N ↦ log (Nat.card {K // stickNumber K ≤ N})) =Theta[N→∞]
      (N ↦ N log N).
  ```

  All floor, positivity, Stirling, and asymptotic estimates in this theorem are
  Lean proofs.
- It also formalizes the sharper coefficient without the optimized arithmetic
  interface.  For every real `c < 2/3`, Lean chooses a sufficiently large
  fixed word length `q`, sets `k = floor(N/(6(q+9)))`, and proves eventually

  ```text
  c * N * log N ≤ log (Nat.card {K // stickNumber K ≤ N}).
  ```

  This is the certified one-sided meaning of the manuscript's
  `N^((2/3+o(1))N)` lower bound.
- `ManuscriptArithmetic.lean` proves the varying-word display with the explicit
  `-(2/3)N log log N + O(N)` deficit. It constructs
  `provedOptimizedDeficitArithmetic` and composes it with the typed lower
  transfer; no further arithmetic input is needed.
- The same module extracts the upper coefficient: for every `c > 3`,
  eventually `log |K_N| ≤ c N log N`.

See [MANUSCRIPT_MAP.md](MANUSCRIPT_MAP.md) for the full declaration map,
including the manuscript arguments outside the formal target. Older
optimized-equivalence wrappers in `AsymptoticCertificate.lean` are alternate
conditional helpers; the publication conclusions use the proved fixed-word
and deficit theorems described above.
