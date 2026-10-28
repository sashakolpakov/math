import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredCanonicalForms
import OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldFiltrationPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicPurity

/-! # Intrinsic Filtered Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicFilteredForms

noncomputable section

/-! # Every original filtered class retains its genuine native filtered closed form -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "NativeModel" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "NativeSpace" => OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular.NativePointManifold X

set_option backward.isDefEq.respectTransparency false in
/-- Actual analytic identity pullback retains the full original filtered class in every degree. -/
theorem originalFiltered_mem_implies_nativeFilteredForm (p n : ℕ)
    (z : (V).complexCohomology n)
    (hz : ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n z)) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p (n : ℤ)) :
    ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms NativeModel NativeSpace n,
      form.val ∈ Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration
        NativeModel NativeSpace n p ∧
      ((V).deRhamBettiIso n).hom ((V).deRhamClass n form) = z := by
  let a := ((V).deRhamBettiIso n).toLinearEquiv.symm z
  have hb : ((V).deRhamBettiIso n).hom a = z :=
    ((V).deRhamBettiIso n).toLinearEquiv.apply_symm_apply z
  have ha : ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n (((V).deRhamBettiIso n).hom a))) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p (n : ℤ) := by rw [hb]; exact hz
  obtain ⟨form, hf, hc⟩ := FilteredCanonicalForms.originalFiltered_mem_implies_canonicalFilteredForm X p n a ha
  let β := Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X)
    (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).contMDiff n form
  refine ⟨β, ?_, ?_⟩
  · exact ManifoldFiltrationPullback.manifoldFormFiltration_pullback (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X)
      (AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph X ∞) n (p : ℤ) form.val hf
  · have hi := IntrinsicPurity.nativeOriginalDeRhamCohomologyIso_inv_formClass X n form
    have he := congrArg (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).toLinearEquiv.symm hc
    change (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).toLinearEquiv.symm
      ((IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).toLinearEquiv a) =
        (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).inv _ at he
    rw [LinearEquiv.symm_apply_apply, hi] at he
    change ((V).deRhamBettiIso n).hom (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass
      NativeModel NativeSpace n β) = z
    rw [← he]
    exact hb

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicFilteredForms
