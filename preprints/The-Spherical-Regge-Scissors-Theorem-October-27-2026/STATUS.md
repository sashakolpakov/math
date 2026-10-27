# Status of the result

Formal-contract revision date: 27 September 2026. Primary-source audit date:
26 September 2026.

The repository now distinguishes three claims:

- The finite Regge algebra and the logical implication from E1--E8 to a
  finite equidecomposition are formalized in Lean.
- The manuscript is self-contained as a conditional argument: every
  non-elementary premise is stated in E1--E8 and mapped to the Lean contract.
- The unconditional spherical Regge scissors theorem is not established
  here, because the exact relative motivic bridge E2--E5 has not been
  constructed or supplied by a cited theorem in that full form.

| Component | Repository status | Trust boundary |
|---|---|---|
| Regge matrix and monomial phase action | Proved in Lean | Geometric realization and volume equality are E1 |
| Gram determinant and rational charts | Polynomial identities proved in Lean | Physical-locus and finite-etale geometric assertions are stated separately |
| Relative quadric coefficient | Explained and typed | Existence/functoriality are E2 |
| Three weight pieces and primitive kernel | Semantics explained; deduction from kernel comparison proved in Lean | Strict filtration, comparison, and vanishing are E3 |
| Relative coproduct and Artin descent | Four-channel algebra and derived fibre primitivity proved in Lean | Six-channel formula, trace, and specialization square are E4 |
| Fibre endpoint | Diagram chase proved in Lean | Linear maps and exact equality with Goncharov's \(c_G\) are E5 |
| Field-level and spherical injections | Used through typed maps and generator comparisons | E6--E7 |
| Suspension, area, volume, and cancellation | Final finite-list witness deduced in Lean | Rationalization and structural scissors statements are E8; Regge volume is E1 |
| Main result | Kernel-checked conditional theorem | Unconditional status awaits E2--E5 |

## Principal conditional claim

For every nondegenerate spherical tetrahedron \(T\subset S^3\), if the
external package E1--E8 is instantiated for a rational chart containing
\(T\) and its elementary Regge mate \(T^R\), then \(T\) and \(T^R\)
admit finite geodesic dissections whose pieces pair by spherical isometries.

No algebraicity assumption is imposed on the individual tetrahedron. The
exact conventions and the complete external package appear at the beginning
of the manuscript.

## Review boundary

Lean's kernel checks the project declarations and the conditional theorem,
not the mathematical truth of values later supplied for the contract. The
source and release checks establish compilation, absence of proof
placeholders and project axioms, documentation consistency, and reproducible
artifacts. They do not replace construction of E2--E5, independent expert
review, or publication.
