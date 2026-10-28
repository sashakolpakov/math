import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartOneTestDerivatives
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedChartPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedAdjointPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantLocality

/-! # One Adjoint Metric Pairs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The two sides of native supported integration have exactly the original global bundle metric pairings. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartAdjoint_one_leftPair
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    inner ℝ (h.projectiveWeightedFormOperator V e i 2 z
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 2 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 2 b).extension z))
      (h.projectiveCovariantCoordinateDerivative V e i 1
        (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 1 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 1 f hf hs a).val) z) =
      ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z *
        (h.globalFormPair V 2 b (h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a)) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re := by
  rw [h.chartFrameTest_covariantDerivativeOne V e he i f hf hs a hz]
  exact h.globalFormPair_coordinates V e he i 2 b _ hz

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartAdjoint_one_rightPair
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    inner ℝ (h.projectiveWeightedFormOperator V e i 1 z
      (h.projectiveCovariantAdjointCoefficients V e i 1
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 2 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 2 b).extension) z))
      (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 1 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 1 f hf hs a).val z) =
      ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z *
        (h.globalFormPair V 1 (h.weightedCovariantChartAdjoint V e he i 1 f hf hs b) a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re := by
  rw [← h.chartCovariantAdjointFrame_coefficients V e he i 1 b hz.1,
    Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e 1 _ hz.1,
    h.projectiveWeightedFormOperator_manifoldPair V e he i 1 _ _ hz,
    h.weightedCovariantChartAdjoint_pair_inFrame V e he i 1 f hf hs a b
      ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, e.map_target hz.1, hz.2⟩,
    Projective.CovectorPair.projectiveFormPointPair_eq_tangentPair,
    Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_apply V u e i 1 f hf hs a ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩,
    Projective.CovectorPair.projectiveTangentCovectorPair_smul_right]
  apply congrArg (fun t : ℂ => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * t.re)
  ring

omit he in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.localizedCovariantOnePair_zero
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2)
    (x : V.analyticSpace) (hx : x ∉ tsupport f) :
    h.globalFormPair V 2 b (h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a)) x = 0 := by
  have hxx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  rw [← h.globalFormPair_conj V 2 b _ x,
    h.globalFormPair_inFrame V 2 _ b x x hxx,
    h.covariantDerivativeOne_localized_zero a f hf x ⟨x, trivial, hxx⟩ hx,
    Holomorphic.AdjointPointPairs.projectiveTangentCovectorPair_zero_left, mul_zero, map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
