import OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport
import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence

/-! # Chart Test Forms -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartTestForms.Constructions

noncomputable section

/-! Compactly supported vector-valued Euclidean test forms lift to actual
global smooth manifold forms with precisely their prescribed coefficients. -/

open Set _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

theorem euclideanChartCoefficients_smulFunction
    (f : V.analyticSpace → ℂ) (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a) z =
      f (MeasureVolume.Constructions.chartCoordinateInverse V e z) • EuclideanForms.Constructions.euclideanChartCoefficients V e n a z := by
  rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic,
    DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
  exact (SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n).map_smul
    (f (MeasureVolume.Constructions.chartCoordinateInverse V e z)) (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))

include he in
theorem exists_projective_chart_test_form
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      (∀ z, SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z = c z) ∧
      ∀ x, x ∉ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport c) → a x = 0 := by
  obtain ⟨η, hηc, hηU, _, hηone⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    hc (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hs
  let f := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η
  have hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he η hηc hηU
  have hfs : tsupport f ⊆ e.source :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_tsupport V e η hηc hηU).trans
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hηU)
  let a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ofSmooth (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f (LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients V e n c))
      ((LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients_smooth V e he n c (c.smooth ⊤).contDiffOn).smulFunction_of_tsupport_subset
        e.open_source hf.contMDiffOn hfs)
  have hcoeff (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z = c z := by
    change EuclideanForms.Constructions.euclideanChartCoefficients V e n
      (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f (LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients V e n c)) z = _
    rw [euclideanChartCoefficients_smulFunction, LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients_inverse V e he n c z hz]
    have hval : f (MeasureVolume.Constructions.chartCoordinateInverse V e z) = η z := by
      change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η (e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = _
      rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, indicator_of_mem (e.map_target hz), e.right_inv hz,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [hval]
    by_cases hzc : z ∈ tsupport c
    · have hηz : η z = 1 := (hηone z hzc).eq_of_nhds
      rw [hηz, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hzc, smul_zero]
  refine ⟨a, fun z => ?_, fun x hx => ?_⟩
  · by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
    · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a.val hz]
      exact hcoeff z hz
    · rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients, indicator_of_notMem hz,
        image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))]
  · by_cases hxe : x ∈ e.source
    · have hz := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hxe
      apply (CodifferentialSupport.Constructions.euclideanChartCoefficients_zero_iff_at V e he n a.val x hxe).mp
      rw [hcoeff _ hz]
      apply image_eq_zero_of_notMem_tsupport
      intro h
      apply hx
      exact ⟨MeasureVolume.Constructions.chartCoordinateForward V e x, h, MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hxe⟩
    · change f x • LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients V e n c x = 0
      have hfx : f x = 0 := by
        exact image_eq_zero_of_notMem_tsupport (fun h => hxe (hfs h))
      rw [hfx]
      exact zero_smul ℂ (LocalAdjointForm.Constructions.chartFormOfEuclideanCoefficients V e n c x)

def projectiveChartTestLift
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  Classical.choose (exists_projective_chart_test_form V e he n c hc hs)

theorem projectiveChartTestLift_coefficients
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (projectiveChartTestLift V e he n c hc hs).val z = c z :=
  (Classical.choose_spec (exists_projective_chart_test_form V e he n c hc hs)).1 z

theorem projectiveChartTestLift_zero
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : V.analyticSpace) (hx : x ∉ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport c)) :
    projectiveChartTestLift V e he n c hc hs x = 0 :=
  (Classical.choose_spec (exists_projective_chart_test_form V e he n c hc hs)).2 x hx

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartTestForms.Constructions
