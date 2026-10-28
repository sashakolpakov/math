import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneAdjointMetricPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.MetricAdjoint
import OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral

/-! # Covariant One Adjoint Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual global bundle metric pairing of the supported native covariant adjoint. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjointOne_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2) :
    (h.formIntegralPair V 2 b (h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a))).re =
      (h.formIntegralPair V 1 (h.weightedCovariantChartAdjoint V e he i 1 f hf hs b) a).re := by
  let C := h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a)
  let Q := h.weightedCovariantChartAdjoint V e he i 1 f hf hs b
  let T := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 1 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 1 f hf hs a).val
  let B := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 2 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 2 b).extension
  let D := h.projectiveCovariantCoordinateDerivative V e i 1
  let M := h.projectiveWeightedFormOperator V e i
  let A := h.projectiveCovariantAdjointCoefficients V e i 1 B
  have hT : ContDiff ℝ ∞ T := Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_smooth V u e he i 1 f hf hs a
  have hTc : HasCompactSupport T := Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_compact V u e i 1 f hf hs a
  have hTs := Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_tsupport V u e i 1 f hf hs a
  have hB : ContDiffOn ℝ ∞ B
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) :=
    ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 2).contDiff.restrict_scalars ℝ).comp_contDiffOn
      (ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
        2 (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 2 b))
  have hL0 (x : V.analyticSpace) (hx : x ∉ tsupport f) : h.globalFormPair V 2 b C x = 0 :=
    h.localizedCovariantOnePair_zero V f hf a b x hx
  have hR0 (x : V.analyticSpace) (hx : x ∉ tsupport f) : h.globalFormPair V 1 Q a x = 0 :=
    h.weightedCovariantChartAdjoint_pair_zero V e he i 1 f hf hs a b x hx
  have hchartL := Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => (h.globalFormPair V 2 b C x).re)
    (Complex.continuous_re.comp (h.globalFormPair_smooth V 2 b C).continuous).aestronglyMeasurable
    (fun x hx => congrArg Complex.re (hL0 x (fun hy => hx (hs hy).1)))
  have hchartR := Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => (h.globalFormPair V 1 Q a x).re)
    (Complex.continuous_re.comp (h.globalFormPair_smooth V 1 Q a).continuous).aestronglyMeasurable
    (fun x hx => congrArg Complex.re (hR0 x (fun hy => hx (hs hy).1)))
  have hleft (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.globalFormPair V 2 b C (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re =
        inner ℝ (M 2 z (B z)) (D T z) := by
    by_cases hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    · exact (h.chartAdjoint_one_leftPair V e he i f hf hs a b hzi).symm
    · have hnot : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∉ tsupport f := fun hx => hzi ⟨hz, (hs hx).2⟩
      have hnotT : z ∉ tsupport T := fun hx => hzi (hTs hx)
      rw [hL0 _ hnot]
      have hD := h.projectiveCovariantCoordinateDerivative_zero_off_support V e i 1 T hnotT
      change D T z = 0 at hD
      rw [hD, inner_zero_right]
      exact mul_zero _
  have hright (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.globalFormPair V 1 Q a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re =
        inner ℝ (M 1 z (A z)) (T z) := by
    by_cases hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
    · exact (h.chartAdjoint_one_rightPair V e he i f hf hs a b hzi).symm
    · have hnot : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∉ tsupport f := fun hx => hzi ⟨hz, (hs hx).2⟩
      have hnotT : z ∉ tsupport T := fun hx => hzi (hTs hx)
      rw [hR0 _ hnot, image_eq_zero_of_notMem_tsupport hnotT, inner_zero_right]
      exact mul_zero _
  have hDzero (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∉ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : D T z = 0 :=
    h.projectiveCovariantCoordinateDerivative_zero_off_support V e i 1 T (fun hx => hz (hTs hx).1)
  have hTzero (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∉ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : T z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx => hz (hTs hx).1)
  calc
    _ = ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, inner ℝ (M 2 z (B z)) (D T z) := by
      rw [h.formIntegralPair_re, ← Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V, hchartL]
      apply setIntegral_congr_fun (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [smul_eq_mul]
      exact hleft z hz
    _ = ∫ z, inner ℝ (M 2 z (B z)) (D T z) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hDzero z hz, inner_zero_right])
    _ = ∫ z, inner ℝ (M 1 z (A z)) (T z) :=
      h.projectiveCovariantAdjointCoefficients_integration V e he i 1 T B hT hB hTc hTs
    _ = ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, inner ℝ (M 1 z (A z)) (T z) := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hTzero z hz, inner_zero_right])
    _ = _ := by
      rw [h.formIntegralPair_re, ← Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V, hchartR]
      apply setIntegral_congr_fun (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [smul_eq_mul]
      exact (hright z hz).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
