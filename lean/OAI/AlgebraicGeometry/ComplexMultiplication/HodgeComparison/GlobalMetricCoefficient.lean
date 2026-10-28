import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactPatchFields
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDirichlet

/-! # Global Metric Coefficient -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient.CM.Construction

noncomputable section

/-! The actual inverse-metric coefficient on global L2 one-form fields.
The global measure already contains the metric volume density. -/

open _root_.MeasureTheory Set
open scoped ContDiff _root_.Manifold

variable {ι : Type*} [Fintype ι]

def varietyInverseMetricOperator (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  InverseMetric.CM.Construction.realBilinearOperator (Metric.CM.Construction.complexGradientMetric b (EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric V e z))

theorem varietyInverseMetricOperator_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    ContDiffOn ℝ ∞ (varietyInverseMetricOperator V e b)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  have hC := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (F := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ)
    (Metric.CM.Construction.complexGradientMetric b)).comp_contDiffOn (EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric_smooth V e he)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ)
    (F := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (InverseMetric.CM.Construction.realBilinearOperator (E := EuclideanSpace ℂ ι))).comp_contDiffOn hC

theorem varietyInverseMetricOperator_continuous_in_chart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    ContinuousOn (fun x => varietyInverseMetricOperator V e b
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))) e.source := by
  apply (varietyInverseMetricOperator_smooth V e he b).continuousOn.comp
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn e.continuousOn)
  intro x hx
  change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact e.map_source hx

def varietyGlobalMetricCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    V.analyticSpace → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  C.patchField (fun i x => varietyInverseMetricOperator V (C.chart i) b
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x)))

theorem varietyGlobalMetricCoefficient_measurable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    AEStronglyMeasurable (varietyGlobalMetricCoefficient V C b) (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  C.patchField_aestronglyMeasurable _ (fun i =>
    (varietyInverseMetricOperator_continuous_in_chart V (C.chart i) (C.chart_mem i) b).mono
      (C.subset_source i))

theorem varietyGlobalMetricCoefficient_bounded (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖varietyGlobalMetricCoefficient V C b x‖ ≤ B :=
  C.patchField_bounded _ (fun i =>
    (varietyInverseMetricOperator_continuous_in_chart V (C.chart i) (C.chart_mem i) b).mono
      (C.subset_source i))

theorem varietyGlobalMetricCoefficient_lower (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, ∀ w : EuclideanSpace ℂ ι,
      a * ‖w‖ * ‖w‖ ≤ inner ℝ (varietyGlobalMetricCoefficient V C b x w) w := by
  have hlocal (i : Fin C.size) : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ C.compactSet i,
      ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤
        inner ℝ (varietyInverseMetricOperator V (C.chart i) b
          ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x)) w) w := by
    let K := MetricChartMeasure.CM.Construction.varietyMetricChartCoordinates V (C.chart i) (C.compactSet i)
    have hK : IsCompact K := MetricMeasureFinite.CM.Construction.varietyMetricChartCoordinates_isCompact V (C.chart i)
      (C.isCompact i) (C.subset_source i)
    have hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V (C.chart i) :=
      fun z hz => ((MetricChartMeasure.CM.Construction.mem_varietyMetricChartCoordinates V (C.chart i) (C.compactSet i) z).mp hz).1
    obtain ⟨a, _, ha, _, hlow, _⟩ := EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric_uniform_bounds V
      (C.chart i) (C.chart_mem i) hK hKU
    refine ⟨a, ha, fun x hx w => ?_⟩
    have hz : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x) ∈ K := by
      dsimp only [K]
      rw [MetricMeasureFinite.CM.Construction.varietyMetricChartCoordinates_eq_image V (C.chart i) (C.subset_source i)]
      exact mem_image_of_mem _ hx
    change _ ≤ inner ℝ (InverseMetric.CM.Construction.realBilinearOperator _ w) w
    rw [InverseMetric.CM.Construction.realBilinearOperator_apply]
    exact Metric.CM.Construction.complexGradientMetric_lower_bound b _ (hlow _ hz) w
  choose a ha hlow using hlocal
  obtain ⟨c, hc, hca⟩ := (isCompact_univ : IsCompact (univ : Set (Fin C.size))).exists_forall_le'
    (continuous_of_discreteTopology.continuousOn : ContinuousOn a univ) (fun i _ => ha i)
  refine ⟨c, hc, fun x w => ?_⟩
  obtain ⟨i, hi⟩ := C.exists_piece x
  unfold varietyGlobalMetricCoefficient
  rw [C.patchField_eq _ hi]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hca i (mem_univ i)) (norm_nonneg w)) (norm_nonneg w)).trans
      (hlow i x (C.piece_subset i hi) w)

theorem varietyGlobalMetricCoefficient_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (x : V.analyticSpace) (u v : EuclideanSpace ℂ ι) :
    inner ℝ (varietyGlobalMetricCoefficient V C b x u) v =
      inner ℝ (varietyGlobalMetricCoefficient V C b x v) u := by
  obtain ⟨i, hi⟩ := C.exists_piece x
  unfold varietyGlobalMetricCoefficient
  rw [C.patchField_eq _ hi]
  have hz : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x) ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V (C.chart i) := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x)) ∈ (C.chart i).target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (C.chart i).map_source (C.piece_subset_source i hi)
  simp only [varietyInverseMetricOperator, InverseMetric.CM.Construction.realBilinearOperator_apply]
  exact Metric.CM.Construction.complexGradientMetric_symmetric b _
    (EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric_symmetric V (C.chart i) (C.chart_mem i) hz) u v

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient.CM.Construction
