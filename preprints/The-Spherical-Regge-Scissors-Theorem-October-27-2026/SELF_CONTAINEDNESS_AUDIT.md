# Self-containedness audit

Audit date: 27 September 2026.

## Result

The manuscript is self-contained as a conditional proof relative to the
numbered package E1--E8. It is not a standalone unconditional proof of the
spherical Regge scissors theorem: construction of the exact relative
motivic bridge E2--E5 remains external work.

This distinction is structural. The manuscript explains what the proposed
motive and every map mean, while Lean checks the implication once those maps
and comparison theorems are supplied. Neither exposition nor a structure
field is evidence that an inhabitant exists for geometric tetrahedra.

## Definition closure

Before their logical use, the manuscript defines or explains:

- spherical scissors classes, reduction, suspension, and finite
  equidecomposition;
- the Regge matrix, phase variables, Laurent monomials, Gram matrices,
  orientation roots, principal opens, and finite-etale double covers;
- motives versus ordinary rational homology, stable totalization, internal
  duality, Tate twists, sign-Artin objects, motivic cohomology, and
  \(K_3\);
- hearts, strict three-step filtrations, frames, reduced coproducts,
  primitive elements, and endpoint extensions; and
- specialization, projective duality, rationalization, and the precise
  source and target of Goncharov's \(c_G\).

The manuscript also explains why replacing motives with complexes of
rational vector spaces would erase the relevant extension group.

## Dependency closure

The external boundary is enumerated before the proof:

- E1: geometric Regge realization, angle/length action, and volume;
- E2: relative framed coefficients and functorial pullback;
- E3: exact graded pieces, strict heart, primitive comparison, and
  \(H^1(U,\mathbf Q(2))\) vanishing;
- E4: relative length--angle coproduct, algebraization, sign-Artin trace
  descent, and the commuting specialization square which transports
  primitivity to the fibre;
- E5: linear specialization and endpoint maps and equality of the specialized
  endpoint with \(c_G\), including signs, frames, twist, and duality;
- E6: field-level injections and projective duality;
- E7: comparison of spherical presentations, including the particular Regge
  generator; and
- E8: additive rationalization and its injectivity, suspension exactness,
  suspension volume, area, and finite cancellation.

No appeal to “standard motivic formalism” is used to cross E2--E5.

## Formal coverage

The Lean development checks the finite matrix, Laurent, determinant, chart,
deck, tensor, kernel, specialization, injectivity, rationalization,
suspension, volume, and cancellation deductions. The field-level primitive
subspace is the actual kernel of a typed coproduct, and the final result is a
finite-list equidecomposition certificate rather than an unnamed proposition.
Deep objects are represented by narrow structures, not global axioms. The
main theorem is universally quantified over a `ProofContract`.

The coverage audit has three safeguards:

1. `formal/coverage.json` classifies every labeled definition, lemma,
   proposition, and theorem in the manuscript.
2. `formal/MANUSCRIPT_MAP.md` explains the corresponding declaration or
   external field and its exact scope.
3. `scripts/check_formal_coverage.py` checks the manuscript labels, Lean
   names, and human-readable map against one another.

The source scan rejects proof placeholders and trust-broadening project
declarations. The axiom check compiles the public theorem list and permits
only Lean's documented logical foundations (`propext`, `Quot.sound`, and
`Classical.choice`), never a project-specific mathematical axiom.

## Items intentionally outside Lean

The project does not formalize real spherical tetrahedra, schemes and their
finite-etale morphisms, a category of relative motives, motivic cohomology,
algebraic \(K\)-theory, Goncharov's quadric complex, or geometric scissors
groups from foundations. Standard geometric observations in Section 2 are
used only to choose the contract's physical point; the theorem-critical
consequences are exposed in E1--E5.

Accordingly, predicates such as “is the alternating face object” and “is a
physical Regge pair” are interpretation obligations supplied by a contract
constructor; Lean does not define their geometric semantics. Their presence
prevents the obligation from disappearing, but only an external
instantiation can prove that the actual geometric objects satisfy them. The
coordinate algebra is checked beside this realization boundary, while E4
states the exact bridge from those coordinates to the motivic channels.

## Verdict

- Definitionally self-contained for a reader: yes.
- Logically self-contained relative to E1--E8: yes.
- Kernel-checked internal implication: yes.
- Kernel-checked construction of E1--E8: no.
- Unconditional proof of the headline theorem: no, pending E2--E5.
