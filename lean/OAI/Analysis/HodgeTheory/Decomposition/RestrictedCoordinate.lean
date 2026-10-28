import OAI.Analysis.HodgeTheory.Decomposition.Coordinate
import OAI.Analysis.HodgeTheory.Decomposition.Form

/-! # Restricted Coordinate -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RestrictedCoordinate.Constructions

noncomputable section

/-! Coordinate L² estimates on compact chart subsets for arbitrary smooth
forms. The form itself need not have support in the chart. -/

open _root_.MeasureTheory Set

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveMetricVolume_setIntegral_chart {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (h : V.analyticSpace → F) (hh : AEStronglyMeasurable h (MeasureVolume.Constructions.projectiveChartMeasure V e)) :
    (∫ x in K, h x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) =
      ∫ z in MeasureVolume.Constructions.chartCoordinateForward V e '' K,
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • h (MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
  classical
  let L := MeasureVolume.Constructions.chartCoordinateForward V e '' K
  have hL : IsCompact L := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe
  have hLU : L ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  have hmem (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      z ∈ L ↔ MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ K := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (hKe hx)]
    · intro hx
      exact ⟨MeasureVolume.Constructions.chartCoordinateInverse V e z, hx, MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hz⟩
  rw [← integral_indicator hK.measurableSet]
  rw [ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he (K.indicator h) (hh.indicator hK.measurableSet)
    (fun x hx => Set.indicator_of_notMem (fun h => hx (hKe h)) h)]
  calc
    _ = ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        L.indicator (fun y => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e y • h (MeasureVolume.Constructions.chartCoordinateInverse V e y)) z := by
      apply setIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • K.indicator h (MeasureVolume.Constructions.chartCoordinateInverse V e z) = _
      by_cases hzk : MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ K
      · rw [Set.indicator_of_mem hzk, Set.indicator_of_mem ((hmem z hz).mpr hzk)]
      · rw [Set.indicator_of_notMem hzk, Set.indicator_of_notMem (fun h => hzk ((hmem z hz).mp h)), smul_zero]
    _ = _ := by rw [setIntegral_indicator hL.measurableSet, inter_eq_right.mpr hLU]

theorem projective_restricted_coordinate_energy (n : ℕ)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    (∫ z in MeasureVolume.Constructions.chartCoordinateForward V e '' K,
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z))
        (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) =
      ∫ x in K, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re ∂ MeasureVolume.Constructions.projectiveMetricVolume V := by
  rw [projectiveMetricVolume_setIntegral_chart V e he hK hKe
    (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re)
    (Complex.continuous_re.comp (MetricCoefficients.Constructions.projectiveFormPointPair_continuous V n a a)).aestronglyMeasurable]
  apply setIntegral_congr_fun (SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe).measurableSet
  rintro z ⟨x, hx, rfl⟩
  exact EuclideanForms.Constructions.euclideanChartCoefficients_weighted_inner V e he n a.val a.val _
    (MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx))

theorem projective_restricted_coordinate_norm_bound (n : ℕ)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      (∫ z in MeasureVolume.Constructions.chartCoordinateForward V e '' K, ‖EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z‖ ^ 2) ≤
        B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ ^ 2 := by
  let L := MeasureVolume.Constructions.chartCoordinateForward V e '' K
  have hL : IsCompact L := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe
  have hLU : L ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  obtain ⟨c, hc, hbound⟩ := CoordinateEstimates.Constructions.projectiveWeightedFormOperator_uniform_lower V e he n hL hLU
  refine ⟨c⁻¹, inv_pos.mpr hc, fun a => ?_⟩
  let u := EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val
  have hu : ContinuousOn u L := (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he n a).continuousOn.mono hLU
  have hni : IntegrableOn (fun z => ‖u z‖ ^ 2) L volume :=
    (hu.norm.pow 2).integrableOn_compact hL
  have hwi : IntegrableOn (fun z => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z)) L volume :=
    ((((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).continuousOn.mono hLU).clm_apply hu).inner hu).integrableOn_compact hL
  have hI : c * (∫ z in L, ‖u z‖ ^ 2) ≤
      ∫ z in L, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hni.const_mul c) hwi hL.measurableSet (fun z hz => hbound z hz (u z))
  rw [projective_restricted_coordinate_energy V e he n hK hKe a] at hI
  have hRe : Integrable (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re) (MeasureVolume.Constructions.projectiveMetricVolume V) :=
    Complex.reCLM.integrable_comp (Form.Constructions.projectiveFormPointPair_integrable V n a a)
  have hglobal := setIntegral_le_integral (s := K) hRe
    (Filter.Eventually.of_forall (fun x => ProjectiveFormMetric.Constructions.projectiveFormPointPair_nonneg V n a.val x))
  have hnorm : (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re ∂ MeasureVolume.Constructions.projectiveMetricVolume V) =
      ‖Form.Constructions.smoothToProjectiveL2 V n a‖ ^ 2 := by
    calc
      _ = (Form.Constructions.projectiveL2Pair V n a a).re := integral_re (Form.Constructions.projectiveFormPointPair_integrable V n a a)
      _ = _ := by
        rw [← Form.Constructions.smoothToProjectiveL2_inner]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hnorm] at hglobal
  have hfinal := mul_le_mul_of_nonneg_left (hI.trans hglobal) (inv_pos.mpr hc).le
  rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hfinal

end

end OAI.Analysis.HodgeTheory.Decomposition.RestrictedCoordinate.Constructions
