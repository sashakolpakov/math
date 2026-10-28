import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.InsertionCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful

/-! # Chart Frame Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameCutoff

noncomputable section

section

/-! A compact subset of an actual bundle chart has an original global smooth cutoff supported in that chart and equal to one on the prescribed compact set. -/

open _root_.TopologicalSpace Filter Set
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions

theorem varietyChartTestScalar_inverse_value (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (η : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = η z := by
  change ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η (e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = _
  rw [ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, Set.indicator_of_mem (e.map_target hz), e.right_inv hz,
    ContinuousLinearEquiv.symm_apply_apply]

theorem exists_holomorphic_chart_frame_cutoff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hs : K ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ f : V.analyticSpace → ℂ, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f ∧
      tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) ∧
      ∀ z ∈ K, f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1 := by
  let U := ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  obtain ⟨η, hηc, hηU, _, hηone⟩ := ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK U.isOpen hs
  have hηbase : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := fun z hz => (hηU hz).1
  let f := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η
  have hf := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he η hηc hηbase
  have hsupport := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_tsupport V e η hηc hηbase
  refine ⟨f, hf, ?_, fun z hz => ?_⟩
  · intro x hx
    have hxim := hsupport hx
    refine ⟨ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hηbase hxim, ?_⟩
    obtain ⟨z, hz, rfl⟩ := hxim
    exact (hηU hz).2
  · exact (varietyChartTestScalar_inverse_value V e η (hs hz).1).trans ((hηone z hz).eq_of_nhds)

end

/-! Actual real global chart cutoffs equal one on a neighborhood of the prescribed compact set. -/

open _root_.TopologicalSpace Filter Set
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions

theorem varietyChartTestScalar_real (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (η : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hη : ∀ z, η z = Complex.ofReal (η z).re) (x : V.analyticSpace) :
    ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η x = Complex.ofReal (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η x).re := by
  by_cases hx : x ∈ e.source
  · simp only [ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, Set.indicator_of_mem hx]
    exact hη _
  · simp only [ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, Set.indicator_of_notMem hx, Complex.zero_re, Complex.ofReal_zero]

theorem exists_real_holomorphic_chart_frame_cutoff_near (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hs : K ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ f : V.analyticSpace → ℂ, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f ∧
      tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) ∧
      (∀ x, f x = Complex.ofReal (f x).re) ∧
      ∀ z ∈ K, (fun w => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e w)) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
  let U := ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  obtain ⟨η, hηc, hηU, hηreal, hηone⟩ := ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK U.isOpen hs
  have hηbase : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := fun z hz => (hηU hz).1
  let f := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e η
  have hf := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he η hηc hηbase
  have hsupport := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_tsupport V e η hηc hηbase
  refine ⟨f, hf, ?_, varietyChartTestScalar_real V e η hηreal, ?_⟩
  · intro x hx
    have hxim := hsupport hx
    refine ⟨ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hηbase hxim, ?_⟩
    obtain ⟨z, hz, rfl⟩ := hxim
    exact (hηU hz).2
  · intro z hz
    have hlocal : (fun w => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e w)) =ᶠ[𝓝 z] η :=
      Filter.Eventually.mono ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds (hs hz).1)
        (fun w hw => varietyChartTestScalar_inverse_value V e η hw)
    exact hlocal.trans (hηone z hz)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameCutoff
