import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.GlobalClassComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalIntegrationClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ClosedGlobalRepresentatives

/-! # Integration Criterion -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntegrationCriterion

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint
open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Original F¹ has its genuine smooth-simplex integration criterion

Both sides use the actual original point space and actual original holomorphic
forms. The cohomology comparison is normalized by actual singular chains.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- Equality with an original holomorphic global class is exactly equality of actual integrals. -/
theorem originalOrdinaryDeRhamGlobalClass_iff (n : ℕ)
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ))
    (w : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) Ω•(X)).homology
      (n : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
          (ReferenceSmooth.GlobalClassComparison.originalOrdinaryConstantCohomologyAddEquiv X n z)) =
      GlobalNaturality.globalSectionsToHypercohomology X Ω•(X) (n : ℤ) w ↔
    HomologicalComplex.homologyMap (OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ) z =
      HomologicalComplex.homologyMap (GlobalIntegrationClasses.originalManifoldSimplexIntegrationInt X) (n : ℤ)
        (HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) (n : ℤ) w) := by
  let i := fun α : H_dR^(n : ℤ)(X) =>
    ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv X (n : ℤ)
      (ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X (n : ℤ) α)
  have hi : Function.Injective i :=
    (ReferenceSmooth.Integration.originalSmoothIntegrationHypercohomologyAddEquiv X (n : ℤ)).injective.comp
      (ReferenceSmooth.Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X (n : ℤ)).injective
  have hs := ReferenceSmooth.GlobalClassComparison.originalSmoothAmbientHyperClass_bijective X n
  have hz := ReferenceSmooth.GlobalClassComparison.originalOrdinaryConstantDeRhamIntegration_hyperClass X n z
  have hw := GlobalIntegrationClasses.originalHolomorphicGlobalIntegration_hyperClass X (n : ℤ) w
  constructor
  · intro h
    apply hs.1
    exact hz.symm.trans ((congrArg i h).trans hw)
  · intro h
    apply hi
    exact hz.trans ((congrArg (ReferenceSmooth.GlobalClassComparison.originalSmoothAmbientHyperClass X (n : ℤ)) h).trans hw.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Original F¹ is exactly the class image of genuinely integrated closed holomorphic one-forms. -/
theorem originalF1_mem_iff_actualIntegration
    (z : (OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology 1) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X 1
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X 1).symm
          (ReferenceSmooth.GlobalClassComparison.originalOrdinaryConstantCohomologyAddEquiv X 1 z)) ∈
        ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 ↔
      ∃ (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).presheaf.obj (Opposite.op ⊤))
        (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).hom.app (Opposite.op ⊤) θ = 0),
        HomologicalComplex.homologyMap (OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) 1 z =
          HomologicalComplex.homologyMap (GlobalIntegrationClasses.originalManifoldSimplexIntegrationInt X) 1
            (HomologicalComplex.homologyMap (GlobalFormMaps.originalHolomorphicGlobalToManifoldInt X) 1
              (ClosedHolomorphicClasses.originalClosedHolomorphicGlobalClass X 1 θ hθ)) := by
  rw [ClosedGlobalRepresentatives.originalF1_mem_iff_closedGlobalSection]
  constructor
  · rintro ⟨θ, hθ, he⟩
    exact ⟨θ, hθ, (originalOrdinaryDeRhamGlobalClass_iff X 1 z
      (ClosedHolomorphicClasses.originalClosedHolomorphicGlobalClass X 1 θ hθ)).mp he.symm⟩
  · rintro ⟨θ, hθ, he⟩
    exact ⟨θ, hθ, ((originalOrdinaryDeRhamGlobalClass_iff X 1 z
      (ClosedHolomorphicClasses.originalClosedHolomorphicGlobalClass X 1 θ hθ)).mpr he).symm⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntegrationCriterion
