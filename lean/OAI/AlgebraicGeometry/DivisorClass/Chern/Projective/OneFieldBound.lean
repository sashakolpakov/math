import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.CurvatureBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.DerivativeIntegralBound

/-! # One Field Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Euclidean chart field norms are bounded by the actual weighted bundle metric on a fixed compact chart set. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Projective.BaseMetricBounds.basePair_metricNormed Projective.BaseMetricBounds.basePair_metricSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveOneField_metric_bound
    {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T)
    (hs : T ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ T, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1,
      ‖a‖ ^ 2 ≤ C * (((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * h.projectiveWeightChart V e i z) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) a a).re := by
  let q := fun z => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re
  have hq : ContinuousOn q T :=
    ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono (fun _ hz => (hs hz).1)).mul
      (Complex.continuous_re.comp_continuousOn ((h.projectiveWeightChart_smooth V e he i).continuousOn.mono hs))
  have hqp (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ T) : 0 < q z := by
    dsimp only [q]
    rw [h.projectiveWeightChart_apply V e i (hs hz), Complex.ofReal_re]
    exact mul_pos (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he (hs hz).1) (h.positive i _)
  have hratio : ContinuousOn (fun z => ‖ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z‖ / q z) T :=
    (((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).continuousOn.mono (fun _ hz => (hs hz).1)).norm).div hq
      (fun z hz => (hqp z hz).ne')
  obtain ⟨R, hR⟩ := hT.bddAbove_image hratio
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz a => ?_⟩
  have hr : ‖ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z‖ ≤ max R 1 * q z :=
    (div_le_iff₀ (hqp z hz)).mp ((hR ⟨z, hz, rfl⟩).trans (le_max_left _ _))
  have hp := OneCovectorMetricBound.oneCovectorMetric_norm_sq_le (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hs hz).1)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hs hz).1) a
  have hn : 0 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) a a).re := by
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic _ 1 _ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he (hs hz).1)
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hs hz).1)]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg 1 _
  have hb := hp.trans (mul_le_mul_of_nonneg_right hr hn)
  rw [h.projectiveWeightChart_apply V e i (hs hz)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  have heq : q z = ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * h.weight i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, (hs hz).2⟩ := by
    dsimp only [q]
    rw [h.projectiveWeightChart_apply V e i (hs hz), Complex.ofReal_re]
    rfl
  rw [heq] at hb
  exact hb.trans_eq (mul_assoc _ _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
