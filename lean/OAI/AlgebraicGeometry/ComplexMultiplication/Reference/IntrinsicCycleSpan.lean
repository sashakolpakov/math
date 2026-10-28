import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenHodgeClasses
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports
import OAI.AlgebraicGeometry.ComplexMultiplication.NormalCoclassComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Intrinsic Cycle Span -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicCycleSpan

noncomputable section

/-! # Transporting finite rational cycles into the unchanged original algebraic span -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ)

theorem originalNativeComponent_mem_span
    (hcomponent : ∀ x : CycleClassMap.OriginalCycleComponent X p,
      NormalCoclassComparison.normalCoclassCoefficient p • EvenHodgeClasses.originalEvenBettiBridge X p
        (CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalCycleClass
          (DimensionCycleSupports.originalDimensionSupport X p x)) = CycleClassMap.originalCycleComponentClass X p x)
    (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (BundledAbelianBridge.originalIntegralProjectiveVariety X) p) :
    EvenHodgeClasses.originalEvenBettiBridge X p (CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalCycleClass D) ∈
      ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p := by
  obtain ⟨x, rfl⟩ := (DimensionCycleSupports.originalDimensionSupportEquiv X p).surjective D
  have hx : CycleClassMap.originalCycleComponentClass X p x ∈ ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p := by
    rw [CycleClassMap.originalCycleClassSpan_eq_span]
    exact Submodule.subset_span ⟨x, rfl⟩
  rw [← hcomponent x] at hx
  have hi := (ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p).smul_mem (NormalCoclassComparison.normalCoclassCoefficient p)⁻¹ hx
  rw [smul_smul, inv_mul_cancel₀ (NormalCoclassComparison.normalCoclassCoefficient_ne_zero p), one_smul] at hi
  exact hi

theorem originalNativeCycle_mem_span
    (hcomponent : ∀ x : CycleClassMap.OriginalCycleComponent X p,
      NormalCoclassComparison.normalCoclassCoefficient p • EvenHodgeClasses.originalEvenBettiBridge X p
        (CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalCycleClass
          (DimensionCycleSupports.originalDimensionSupport X p x)) = CycleClassMap.originalCycleComponentClass X p x)
    (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (BundledAbelianBridge.originalIntegralProjectiveVariety X) p) :
    EvenHodgeClasses.originalEvenBettiBridge X p
        (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass
          (BundledAbelianBridge.originalIntegralProjectiveVariety X) p z) ∈ ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p := by
  rw [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass_apply]
  simp only [Finsupp.sum, map_sum, map_smul]
  exact Submodule.sum_mem _ (fun D _ => (ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p).smul_mem _
    (originalNativeComponent_mem_span X p hcomponent D))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicCycleSpan
