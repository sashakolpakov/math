import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Iso Principal Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoPrincipalDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual rational principal divisors under scheme isomorphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (e : X ≅ Y)

theorem schemeIsoPrincipalDivisor_push (g : Y.functionField) :
    Finsupp.mapDomain e.hom (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom g)) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y g := by
  ext y
  obtain ⟨x, rfl⟩ := (inferInstance : Surjective e.hom).surj y
  rw [Finsupp.mapDomain_apply_of_injective e.hom.isClosedEmbedding.injective,
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.ord_openImmersion]

theorem schemeIsoPrincipalDivisor_pull (g : Y.functionField) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom g) =
      Finsupp.mapDomain e.inv (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y g) := by
  rw [← schemeIsoPrincipalDivisor_push e g, ← Finsupp.mapDomain_comp]
  have h : (e.inv : Y → X) ∘ (e.hom : X → Y) = id := by
    funext x
    exact congrArg (fun k : X ⟶ X => k x) e.hom_inv_id
  rw [h, Finsupp.mapDomain_id]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoPrincipalDivisor.BundleCycles
