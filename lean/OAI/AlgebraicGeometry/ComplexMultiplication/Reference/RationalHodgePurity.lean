import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicFilteredForms
import OAI.AlgebraicGeometry.ComplexMultiplication.IntegralFilteredComponentForms
import OAI.AlgebraicGeometry.ComplexMultiplication.IntegralComponentPurity
import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveRationalFilteredClasses

/-! # Rational Hodge Purity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalHodgePurity

noncomputable section

/-! # Original rational filtered classes have the unchanged geometric Hodge type -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- The actual original filtration suffices for genuine rational `(p,p)` purity. -/
theorem originalRationalFiltered_implies_nativeHodge (p : ℕ)
    (a : (V).rationalCohomology (p + p))
    (ha : ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X ((p + p : ℕ) : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X (p + p)).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X (p + p)
          ((V).rationalCohomologyInclusion (p + p) a))) ∈
            ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p ((p + p : ℕ) : ℤ)) :
    (V).IsRationalHodgeClass p a := by
  obtain ⟨form, hf, hc⟩ := IntrinsicFilteredForms.originalFiltered_mem_implies_nativeFilteredForm X p (p + p)
    ((V).rationalCohomologyInclusion (p + p) a) ha
  have hfamily := IntegralFilteredComponentForms.integralFilteredComponentForm_filtered (V) (p + p) p form hf
  have hclass := IntegralFilteredComponentForms.integralFilteredComponentForm_class (V) (p + p) form
  have hfiltered : (V).rationalCohomologyInclusion (p + p) a ∈
      Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti (V).presentation (p + p) p := by
    refine ⟨IntegralFilteredComponentForms.integralFilteredComponentForm (V) (p + p) form, hfamily, ?_⟩
    exact hclass.trans hc
  exact IntegralComponentPurity.integral_presentationPure_implies_pure (V) p p _
    (ProjectiveRationalFilteredClasses.projectiveRationalFiltered_mem_pure (V).presentation p a hfiltered)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalHodgePurity
