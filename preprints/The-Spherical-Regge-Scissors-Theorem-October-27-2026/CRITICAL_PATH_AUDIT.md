# Critical-path audit

This is the dependency map for the conditional proof. “Lean” means the
declaration is kernel checked in this repository. “External” means a named
field of the E1--E8 proof package must be supplied; it is not a global Lean
axiom.

## 1. Geometric input — external E1

Start with a nondegenerate spherical tetrahedron and one elementary Regge
mate. E1 supplies realization of the mate, the common Regge matrix on the
four moving angles and lengths, and equality of volume.

## 2. Phase-coordinate algebra — Lean

Exponentiation changes the additive formula to
\(a_i\mapsto\tau/a_i\), with \(\tau^2=\prod_i a_i\). Lean proves that
this preserves the phase relation and is involutive. It also proves symmetry,
orthogonality, and involutivity of \(R=\frac12J-I\).

## 3. Determinant and orientation charts — Lean plus geometric boundary

Lean expands the actual \(4\times4\) Gram determinant, proves the two
coefficient polynomials invariant under the monomial Regge substitution, and
checks both rational chart inverses and their cover on \(sw\ne0\). It also
checks the fixed-phase quadratic, discriminant, inverse/deck formula, and deck
involution. Smoothness, finite etaleness as schemes, positivity of the
physical Gram matrix, and placement of a physical pair on the open are
standard geometric assertions rather than objects modeled in Lean.

## 4. Relative coefficient — external E2

E2 supplies the two relative framed coefficients over each rational chart,
their reduced coproduct map, and pullback to a complex point. The manuscript
defines the intended four-term face totalization
\(\operatorname{RHom}(\operatorname{Tot}(M(\text{faces})),\mathbb
Q_U)(2)\), but does not infer its existence from an ordinary complex of
rational vector spaces.

## 5. Strict three-weight kernel — external E3, deduction in Lean

E3 states the intended graded pieces
\[
\mathbb Q(0),\qquad
\mathbb Q(1)^{\oplus5}\oplus\chi(1),\qquad
\mathbb Q(2),
\]
strictness of the filtration, identification of the primitive kernel with
\(H^1(U,\mathbb Q(2))\), and vanishing of that group. Given the resulting
kernel equivalence, Lean proves that a class with zero reduced coproduct is
zero.

## 6. Coproduct comparison — external E4, cancellation in Lean

E4 supplies the exact relative formula \(\sum_e L_e\otimes A_e\), its
factor order and complementary indexing, normalized twisted-trace
descent for the nonsplit sign-Artin channel, and a commuting specialization
square into the field-level quadric coproduct. Its typed channel data expose
the two common fixed terms and the four moving half-phase terms. Lean proves
\(H^tH=4I\), derives the normalized tensor equality, passes it through the
external coproduct formulas, and concludes that the universal defect is
primitive. It then uses the commuting square to construct the fibre-kernel
membership proof required by \(c_G\). Thus neither Regge cancellation nor
fibre primitivity is assumed as an untyped label.

## 7. Universal vanishing — E3 plus Lean

The Lean proof combines the coproduct equality from Step 6 with E3's
primitive-kernel comparison and vanishing. The universal framed defect is
therefore zero, conditional on E2--E4.

## 8. Fibre comparison — external E5

E5 supplies linear specialization and endpoint maps and says that the
endpoint of the specialized relative class is exactly
Goncharov's \(c_G\) of the dual quadric-scissors defect, with the same
frames, signs, duality, and Tate twist. Equality of periods or regulators
would not suffice; equality of classes is the named obligation.

## 9. Return to spherical scissors — external E6--E8, deduction in Lean

E6 supplies the field-level injectivity statements, duality, and its generator
compatibility; E7 identifies the spherical presentation and the particular
Regge defect; E8 supplies injective rationalization, exactness at the full
scissors group, the suspension-volume identity, area injectivity, and finite
cancellation.
Lean performs all specialization, injectivity, suspension, volume, and final
equidecomposition deductions.

## Audit conclusion

Every transition is either a compiled Lean declaration or a specifically
named E1--E8 field. The conditional implication is closed and
self-contained relative to those fields. A standalone unconditional proof
still requires construction of E2--E5; the repository no longer describes
that literature gap as a completed internal step.
