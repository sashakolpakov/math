import OAI.Analysis.HodgeTheory.Decomposition.CoordinateEstimates
import OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.LocalMetric
import OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral
import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm

/-! # Coordinate -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Coordinate.Constructions

noncomputable section

/-! Comparison of genuine manifold L² norms with Euclidean coefficient L²
norms for forms supported in compact chart subsets. -/

open scoped ContDiff _root_.Manifold
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projective_supported_coordinate_energy
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ x, x ∉ e.source → a x = 0) :
    (Form.Constructions.projectiveL2Pair V n a a).re =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z)) (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z) := by
  have hchart := ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re)
    (Complex.continuous_re.comp (MetricCoefficients.Constructions.projectiveFormPointPair_continuous V n a a)).aestronglyMeasurable
    (fun x hx => by rw [LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V n a.val a.val x (ha x hx)]; rfl)
  change RCLike.re (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  rw [← integral_re (Form.Constructions.projectiveFormPointPair_integrable V n a a)]
  change (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  rw [hchart]
  calc
    _ = ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z))
          (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z) := by
      apply setIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [smul_eq_mul, SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a.val hz,
        EuclideanForms.Constructions.euclideanChartCoefficients_weighted_inner V e he n a.val a.val z hz]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [show SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z = 0 from Set.indicator_of_notMem hz _,
        inner_zero_right])

theorem projective_supported_coordinate_norm_bound
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      (∀ x, x ∉ K → a x = 0) →
      c * (∫ z, ‖SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z‖ ^ 2) ≤ (Form.Constructions.projectiveL2Pair V n a a).re := by
  let L := MeasureVolume.Constructions.chartCoordinateForward V e '' K
  have hL : IsCompact L := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe
  have hLU : L ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro z ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  obtain ⟨c, hc, hbound⟩ := CoordinateEstimates.Constructions.projectiveWeightedFormOperator_uniform_lower V e he n hL hLU
  refine ⟨c, hc, fun a ha => ?_⟩
  let u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val
  have huc : HasCompactSupport u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n a.val hK hKe ha
  have hu : ContDiff ℝ ∞ u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_smooth V e he n a hK hKe ha
  have hs : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e n a.val hK hKe ha
  have hnc : HasCompactSupport (fun z => ‖u z‖ ^ 2) := huc.mono (by
    intro z hz hzero
    apply hz
    simp only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)])
  have hni : Integrable (fun z => ‖u z‖ ^ 2) volume :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hnc
  have hwi : Integrable (fun z => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z)) volume :=
    LocalAdjointForm.Constructions.smooth_inner_test_integrable volume _ u (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).clm_apply hu.contDiffOn) hu huc hs
  rw [projective_supported_coordinate_energy V e he n a (fun x hx => ha x (fun h => hx (hKe h))),
    ← integral_const_mul]
  apply integral_mono (hni.const_mul c) hwi
  intro z
  by_cases hz : z ∈ L
  · exact hbound z hz (u z)
  · have hz0 : u z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz
        (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport V e n a.val hK hKe ha h))
    dsimp only
    change c * ‖u z‖ ^ 2 ≤ inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (u z)) (u z)
    rw [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, inner_zero_right]

end

end OAI.Analysis.HodgeTheory.Decomposition.Coordinate.Constructions
