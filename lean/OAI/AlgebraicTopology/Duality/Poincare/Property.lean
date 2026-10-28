import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap

/-! # Property -/

namespace OAI.AlgebraicTopology.Duality.Poincare.Property

/-!
# The precise induction property for canonical complex Poincare duality

The maps in this property are the already constructed cap products with
the proved canonical complex orientation. In addition to complementary-degree
isomorphisms, the property records actual compact-support cohomology vanishing
above the real dimension. This is the endpoint information needed by
Mayer--Vietoris induction; it is not an assumption attached to the manifold.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

/-- Canonical cap duality in every complementary degree, together with its
out-of-range compact-support cohomology vanishing. -/
def HasCanonicalPoincareDuality (d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] : Prop :=
  (∀ (p q : ℕ) (hpq : p + q = 2 * d),
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq)) ∧
  (∀ p : ℕ, 2 * d < p →
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p))

namespace HasCanonicalPoincareDuality

variable {d : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The isomorphism assertion concerns precisely the canonical cap map. -/
theorem cap_isIso (h : HasCanonicalPoincareDuality d M)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq) :=
  h.1 p q hpq

/-- The induction property includes the actual higher cohomology vanishing
needed at the top endpoint of the cap-product diagram. -/
theorem cohomology_isZero (h : HasCanonicalPoincareDuality d M)
    (p : ℕ) (hp : 2 * d < p) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :=
  h.2 p hp

end HasCanonicalPoincareDuality

end OAI.AlgebraicTopology.Duality.Poincare.Property
