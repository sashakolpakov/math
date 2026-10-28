import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartIntegralBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ZeroChartPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PotentialChartPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogPointCentered

/-! # Metric Point Estimate -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The original modified bundle norm controls the actual logarithmically weighted local scalar coefficient, uniformly in the potential and regularization parameter. -/

open _root_.MeasureTheory _root_.Metric Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedZeroChart_integral_bound
    {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hs : K ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (m : ℕ) (ε : ℝ), 0 < ε →
      ∀ (φ : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0),
      ball x (Real.sqrt ε) ⊆ K →
      DiffContOnCl ℂ (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a) (ball x (Real.sqrt ε)) →
      (∀ z ∈ ball x (Real.sqrt ε), Real.exp (ScalarPotentialFunctions.realPotentialScalar φ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) =
        ((ε + ‖z - x‖ ^ 2) ^ m)⁻¹) →
      c * (∫ z in ball x (Real.sqrt ε),
        ((ε + ‖z - x‖ ^ 2) ^ m)⁻¹ * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2) ≤
          ((h.withPotential φ).formIntegralPair V 0 a a).re := by
  obtain ⟨c, hc, hb⟩ := h.projectiveZeroChart_compact_lower V e he i hK hs
  refine ⟨c, hc, fun x m ε hε φ a hball ha hφ => ?_⟩
  let W : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ := fun z => ((ε + ‖z - x‖ ^ 2) ^ m)⁻¹
  have hW : Continuous W := by
    simpa only [Function.comp_def, RegularizedLogWeight.regularizedNegativeLog_exp x m hε] using!
      Real.continuous_exp.comp (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε).continuous
  have hWpos (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : 0 ≤ W z :=
    inv_nonneg.mpr (pow_nonneg (add_nonneg hε.le (sq_nonneg _)) m)
  have hac : ContinuousOn (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a) (closedBall x (Real.sqrt ε)) := by
    simpa only [closure_ball x (Real.sqrt_pos.mpr hε).ne'] using ha.2
  have hwi : IntegrableOn (fun z => W z * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2)
      (ball x (Real.sqrt ε)) :=
    ((hW.continuousOn.mul (hac.norm.pow 2)).integrableOn_compact
      (isCompact_closedBall x _)).mono_set ball_subset_closedBall
  have hD : ball x (Real.sqrt ε) ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := fun z hz => (hs (hball hz)).1
  have hpi := ((h.withPotential φ).projectiveGlobalPair_integrable V e he 0 a).mono_set hD
  calc
    _ = ∫ z in ball x (Real.sqrt ε), c * (W z * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2) :=
      (integral_const_mul c _).symm
    _ ≤ ∫ z in ball x (Real.sqrt ε), ((h.withPotential φ).projectiveGlobalPair V e 0 a a z).re := by
      apply integral_mono_ae (hwi.const_mul c) hpi
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      rw [h.withPotential_projectiveGlobalPair_re V e φ 0 a a z, hφ z hz]
      have hp := mul_le_mul_of_nonneg_left (hb z (hball hz) a) (hWpos z)
      change W z * (c * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2) ≤
        W z * (h.projectiveGlobalPair V e 0 a a z).re at hp
      simpa only [mul_left_comm c (W z)] using hp
    _ ≤ _ := (h.withPotential φ).projectiveGlobalPair_integral_le V e he 0 a hD

end

/-! Actual point evaluation is small when an original smooth line section is locally holomorphic and has a bounded original logarithmically modified metric norm. -/

open _root_.MeasureTheory _root_.Metric Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.MetricPointEstimate.varietyEuclideanModel_real_finrank (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Module.finrank ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) = 2 * V.complexDimension := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), Complex.finrank_real_complex]
  simp

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.logarithmic_metric_point_estimate
    {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hs : K ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (ε : ℝ), 0 < ε →
      ∀ (φ : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0),
      ball x (Real.sqrt ε) ⊆ K →
      DiffContOnCl ℂ (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a) (ball x (Real.sqrt ε)) →
      (∀ z ∈ ball x (Real.sqrt ε), Real.exp (ScalarPotentialFunctions.realPotentialScalar φ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) =
        ((ε + ‖z - x‖ ^ 2) ^ (V.complexDimension + 1))⁻¹) →
      c * ((volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).real (ball 0 1) *
        ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a x‖ ^ 2) ≤
          2 ^ (V.complexDimension + 1) * ε * ((h.withPotential φ).formIntegralPair V 0 a a).re := by
  have H := h.weightedZeroChart_integral_bound V e he i hK hs
  let c := H.choose
  have hc : 0 < c := H.choose_spec.1
  refine ⟨c, hc, fun x ε hε φ a hball ha hφ => ?_⟩
  let I := ∫ z in ball x (Real.sqrt ε),
    ((ε + ‖z - x‖ ^ 2) ^ (V.complexDimension + 1))⁻¹ * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2
  have hI : c * I ≤ ((h.withPotential φ).formIntegralPair V 0 a a).re :=
    H.choose_spec.2 x (V.complexDimension + 1) ε hε φ a hball ha hφ
  have hp := Holomorphic.LogPointCentered.holomorphic_log_point_centered V.complexDimension (Holomorphic.MetricPointEstimate.varietyEuclideanModel_real_finrank V)
    x (Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a) hε ha I le_rfl
  calc
    _ ≤ c * (2 ^ (V.complexDimension + 1) * ε * I) := mul_le_mul_of_nonneg_left hp hc.le
    _ = (2 ^ (V.complexDimension + 1) * ε) * (c * I) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (mul_nonneg (pow_nonneg (by norm_num) _) hε.le)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
