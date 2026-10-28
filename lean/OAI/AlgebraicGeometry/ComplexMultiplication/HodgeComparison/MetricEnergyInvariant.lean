import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange

/-! # Metric Energy Invariant -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricEnergyInvariant.CM.Construction

noncomputable section

/-! The genuine global projective metric energy agrees pointwise with
the inverse-metric covector pairing in every actual chart. -/

open Set

theorem positive_metric_pullback_surjective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B D : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBD : ∀ u v : E, B u v = D (T u) (T v)) : Function.Surjective T := by
  have hzero (u : E) (hu : T u = 0) : u = 0 := by
    by_contra hne
    have hp := hB u hne
    rw [hBD u u, hu, map_zero] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hinj : Function.Injective T := by
    intro u v h
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, h, sub_self]
  exact (LinearMap.injective_iff_surjective (f := T.toLinearMap)).mp hinj

theorem varietyEuclideanMetric_at_point_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {x : V.analyticSpace} (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    EuclideanMetric.CM.Construction.varietyEuclideanMetric V e ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) =
      MetricJacobian.CM.Construction.pullbackBilinear (EuclideanMetric.CM.Construction.varietyEuclideanMetric V f ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (f x)))
        (OneFormFrameChange.CM.Construction.varietyEuclideanConjugateOperator V (fderiv ℝ (f ∘ e.symm) (e x))) := by
  have hz : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x) ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact e.map_source hex
  have hfz : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))) ∈ f.source := by
    rwa [ContinuousLinearEquiv.apply_symm_apply, e.left_inv hex]
  have h := MetricJacobian.CM.Construction.varietyEuclideanMetric_transition V e f he hf hz hfz
  rw [(MetricJacobian.CM.Construction.varietyEuclideanTransition_hasFDerivAt V e f he hf hz hfz).fderiv] at h
  simpa only [MetricJacobian.CM.Construction.varietyEuclideanTransition, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
    e.left_inv hex, OneFormFrameChange.CM.Construction.varietyEuclideanConjugateOperator] using h

theorem varietyInverseMetricOperator_at_point_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {x : V.analyticSpace} (hex : x ∈ e.source) (hfx : x ∈ f.source) (u v : EuclideanSpace ℂ ι) :
    inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator V e b ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))
      (OneFormFrameChange.CM.Construction.varietyOneFormFrameChange V b e f x u)) (OneFormFrameChange.CM.Construction.varietyOneFormFrameChange V b e f x v) =
    inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator V f b ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (f x)) u) v := by
  let B := EuclideanMetric.CM.Construction.varietyEuclideanMetric V e ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))
  let D := EuclideanMetric.CM.Construction.varietyEuclideanMetric V f ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (f x))
  let T := OneFormFrameChange.CM.Construction.varietyEuclideanConjugateOperator V (fderiv ℝ (f ∘ e.symm) (e x))
  have hBD : ∀ u v, B u v = D (T u) (T v) := by
    intro u v
    change EuclideanMetric.CM.Construction.varietyEuclideanMetric V e ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) u v = _
    rw [varietyEuclideanMetric_at_point_transition V e f he hf hex hfx]
    rfl
  have hB : ∀ u, u ≠ 0 → 0 < B u u := by
    apply EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact e.map_source hex
  have hD : ∀ u, u ≠ 0 → 0 < D u u := by
    apply EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V f hf
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (f x)) ∈ f.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact f.map_source hfx
  simp only [GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator, InverseMetric.CM.Construction.realBilinearOperator_apply]
  exact CovectorMetric.CM.Construction.complexInverseMetric_transition b B D hB hD T
    (positive_metric_pullback_surjective B D T hB hBD) hBD u v

theorem varietyGlobalMetricCoefficient_form_energy (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {x : V.analyticSpace} (hx : x ∈ e.source) :
    inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b form x))
      (GlobalLp.CM.Construction.varietyOneFormField V C b other x) =
      inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator V e b ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))
        (GlobalLp.CM.Construction.varietyOneFormInChart V b e form x)) (GlobalLp.CM.Construction.varietyOneFormInChart V b e other x) := by
  obtain ⟨i, hi⟩ := C.exists_piece x
  have hA : GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x =
      GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator V (C.chart i) b ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (C.chart i x)) :=
    C.patchField_eq _ hi
  have hF : GlobalLp.CM.Construction.varietyOneFormField V C b form x = GlobalLp.CM.Construction.varietyOneFormInChart V b (C.chart i) form x := C.patchField_eq _ hi
  have hG : GlobalLp.CM.Construction.varietyOneFormField V C b other x = GlobalLp.CM.Construction.varietyOneFormInChart V b (C.chart i) other x := C.patchField_eq _ hi
  rw [hA, hF, hG, OneFormFrameChange.CM.Construction.varietyOneFormInChart_transition V b e (C.chart i) he (C.chart_mem i) form hx (C.piece_subset_source i hi),
    OneFormFrameChange.CM.Construction.varietyOneFormInChart_transition V b e (C.chart i) he (C.chart_mem i) other hx (C.piece_subset_source i hi)]
  exact (varietyInverseMetricOperator_at_point_transition V b e (C.chart i) he (C.chart_mem i)
    hx (C.piece_subset_source i hi) _ _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricEnergyInvariant.CM.Construction
