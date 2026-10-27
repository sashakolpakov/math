# Lean formalization

**Discussions and model prompting:** Alexander Kolpakov (UATX).

This directory machine-checks the manuscript's finite algebra and its
conditional implication chain. It does **not** implement a theory of motives,
motivic cohomology, algebraic \(K\)-theory, Goncharov's quadric complex, or
spherical scissors groups in Mathlib.

The main result is **SphericalReggeScissors.spherical_regge_scissors**. It
returns a nonempty **FiniteEquidecomposition** certificate containing two
finite piece lists, proofs that they decompose the two tetrahedra, and a
pairwise-isometry proof. It is
universally quantified over a
**SphericalReggeScissors.ProofContract**. Supplying such a value means
supplying every external theorem and compatibility statement used by the
paper. A structure field is an ordinary hypothesis, not a global Lean axiom.

## Build

The project pins Lean and Mathlib:

- Lean v4.32.2
- Mathlib commit 905b95818eb32af7874a58b427f50c1711a5e96c

From this standalone package directory:

~~~sh
lake exe cache get
lake build
~~~

The standalone verification also checks forbidden declarations and the
output of the axiom audit:

~~~sh
make verify
~~~

## Modules

- **ReggeMatrix.lean** proves the \(4\times4\) Regge involution,
  orthogonality, eigenspace formulas, and \(H^tH=4I\).
- **PhaseAction.lean** proves that \(u\mapsto\tau/u\) preserves
  \(\tau^2=abcd\) and is involutive in an arbitrary commutative group.
- **OrientationChart.lean** proves the algebra of both rational conic charts
  and the fixed-phase polynomial and deck transformation.
- **CoproductAlgebra.lean** proves the four-channel bilinear and tensor
  cancellation from \(H^tH=4I\).
- **ExternalInputs.lean** declares the typed trust boundary.
- **ThreeWeight.lean** proves the primitive-kernel and relative-defect
  deductions from that boundary.
- **Scissors.lean** proves the specialization/injectivity diagram chase and
  the suspension--volume--area argument.
- **Main.lean** assembles the conditional theorem and prints its axiom
  dependencies.
- **ContractAudit.lean** supplies an inhabited finite model of the complete
  contract and a countermodel showing that Regge involutivity plus equal
  volume alone do not imply scissors equality.

## What the external contract means

The carrier types in the Lean structures deliberately expose only the
operations used by the implication. Their intended mathematical meanings are:

| Lean component | Intended mathematics |
|---|---|
| **GeometricReggeInputs** and its two witnesses in **ProofContract** | E1's physical-pair and angle/length-action certificates; volume is a separate equality |
| **MotivicInputs.RelativeObject**, **coefficient** | the actual relative alternating-face objects and their framed coefficients |
| **isAlternatingFaceObject**, **hasExactThreeGradedPieces**, **strict_three_weight_heart_constructed** | separate certificates for the face construction, exact (0,1,2) graded pieces, and strict heart |
| **MotivicInputs.coproduct** | reduced middle coproduct on relative framed coefficients |
| **MotivicInputs.primitiveComparison** | \(\ker\bar\Delta\cong H^1(U,\mathbf Q(2))\) |
| **MotivicInputs.h1_vanishes** | the Garkusha--Borel vanishing on the rational chart |
| **CoproductBridge.relativeOriginal**, **relativeReggeMate** | coefficients of the two relative oriented quadric face objects |
| **split_formula_original**, **split_formula_reggeMate** | exact relative coproduct/cross-ratio identification |
| **finite_etale_sign_trace_injective** | descent, including the nonsplit sign-Artin channel |
| **movingLeft**, **movingRight**, and the four fixed-channel fields | the six explicit channels on a splitting cover; the mate is forced to use the checked Regge transform |
| **SpecializationInputs.specialize** | pullback of the relative coefficient to a complex point |
| **SpecializationInputs.endpoint** | endpoint extension in \(H^1(\mathbf C,\mathbf Q(2))\) |
| **SpecializationInputs.quadricCoproduct**, **goncharov** | the field-level coproduct and Goncharov's \(c_G\), whose domain is literally its kernel |
| **SpecializationInputs.middleSpecialize**, **quadric_coproduct_specialization** | the commuting square from which Lean derives fibre primitivity |
| **fibre_endpoint_eq_cG** | the sign-, frame-, twist-, and duality-compatible fibre comparison |
| **SpecializationInputs.duality** | projective duality on quadric-scissors classes |
| **SpecializationInputs.spherical** | Goncharov's injection from his rational spherical presentation to quadric classes |
| **ProofContract.presentationComparison** | E7's explicit isomorphism from the rationalized geometric reduced group to Goncharov's presentation |
| **ScissorsInputs.rationalize**, **rationalization_injective** | the explicit passage from the geometric reduced group to its rationalization |
| **ScissorsInputs** | suspension exactness, rationalization, area classification, volume, and cancellation to **FiniteEquidecomposition** |

The manuscript additionally spells out the geometric obligations which
produce these Lean interfaces: construction of the relative face motive,
its exact three graded pieces, a strict three-weight heart, Artin trace
compatibility, and base change to Goncharov's field-level coefficient. The
first three have separate certificate fields in the contract; none of these
obligations is constructed by Lean or follows from ordinary rational homology.
The rational carrier types and their comparison maps are respectively
\(\mathbf Q\)-modules and linear maps in Lean; the three integral scissors
carriers remain additive groups.

The abstract geometric predicates in the contract are interpretation
obligations, not definitions smuggled in under mathematical names. A model
must prove that its actual face objects, physical tetrahedra, decompositions,
and piece isometries satisfy them. The exhaustive assignment of all contract
fields to E1--E8 is recorded in **contract_map.json** and checked by
**scripts/check_contract_parity.py**.

## Why motives are not modeled as vector-space complexes

Rational vector spaces form a semisimple category. Consequently their
first extension groups vanish and every bounded complex splits into its
cohomology. Replacing the proposed motivic object by a plain rational complex
would therefore erase the endpoint extension whose class is meant to lie in
\(H^1(U,\mathbf Q(2))\), or equivalently the relevant weight-two part of
\(K_3\). The formalization instead treats the existence and comparison of
that extension as an explicit external hypothesis and checks everything
deduced from it.

## Reading the result correctly

The theorem **spherical_regge_scissors C** proves the conclusion for any
supplied **ProofContract C**. It does not construct a contract for geometric
spherical tetrahedra. Thus it certifies:

> The manuscript's conclusion follows from its named external statements
> and its checked internal algebra.

It does not yet certify:

> The external relative-motivic bridge exists with the required
> compatibilities.

See [MANUSCRIPT_MAP.md](MANUSCRIPT_MAP.md) for the declaration-by-declaration
boundary.

This external package retains its own Lean 4.32.2 and exact Mathlib pins.
It is built separately from the parent library, with no parent Comparator
target. The coverage and contract checks also read the adjacent
[contributed manuscript](../../preprints/The-Spherical-Regge-Scissors-Theorem-October-27-2026/README.md).
[Provenance](PROVENANCE.md) records source and export adaptations.
