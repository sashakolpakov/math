import OAI.AlgebraicGeometry.Cycle.FundamentalClass
import OAI.AlgebraicGeometry.Hodge.FiltrationId

/-! # Core -/

namespace OAI.AlgebraicGeometry.Foundations

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-!
# The Hodge conjecture

This file states (but does not prove!) the Hodge conjecture.

The Hodge conjecture says that, for every nonsingular complex projective variety `X` and natural
number `p`, every rational Hodge class of degree `2p` on `X` is a rational linear combination of
classes of algebraic subvarieties of `X` of codimension `p`.

## References

[P. Deligne, *The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

/-- Statement of the **Hodge conjecture**.

For every nonsingular complex projective variety `X` and natural number `p`, every rational Hodge
class of degree `2p` on `X` is a rational linear combination of classes of algebraic subvarieties of
`X` of codimension `p`. The algebraic subspace is `algebraicCycleClassSpan`, the span of the
component classes of `Cycle.FundamentalClass` indexed by the points of codimension `p`. -/
 def Core : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ),
    Hdg^p(X; ℚ) ≤ ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p

end OAI.AlgebraicGeometry.Foundations
