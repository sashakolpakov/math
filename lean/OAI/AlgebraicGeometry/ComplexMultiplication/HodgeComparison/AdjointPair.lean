import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPointPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricEnergyInvariant

/-! # Adjoint Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPair.CM.Construction

noncomputable section

/-! The global scalar and one-form L2 pairings used by the formal adjoint
are exactly the real pairings of the scalar Poisson construction. -/

open _root_.MeasureTheory Set

theorem adjointPointPair_zero_re (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (x : V.analyticSpace) :
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 0 a.val c.val x).re =
      inner ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar a x) (HolomorphicPrimitive.CM.Construction.zeroFormScalar c x) := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ _
  have hx : x ∈ e.source := mem_chart_source _ _
  let z := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)
  have hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact e.map_source hx
  have h := AdjointPointPair.CM.Construction.adjointChartPair_zero_re V e he z hz (a.val.inChart e (e x)) (c.val.inChart e (e x))
  have hval (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
      f.val.inChart e (e x) 0 = HolomorphicPrimitive.CM.Construction.zeroFormScalar f x := by
    change f (e.symm (e x)) _ = f x 0
    rw [e.left_inv hx]
    exact congrArg (f x) (Subsingleton.elim _ _)
  rw [hval a, hval c] at h
  simpa only [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair, z, ContinuousLinearEquiv.apply_symm_apply] using h

theorem adjointPointPair_one_re (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (x : V.analyticSpace) :
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 a.val c.val x).re =
      inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b a x))
        (GlobalLp.CM.Construction.varietyOneFormField V C b c x) := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ _
  have hx : x ∈ e.source := mem_chart_source _ _
  let z := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)
  have hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact e.map_source hx
  rw [MetricEnergyInvariant.CM.Construction.varietyGlobalMetricCoefficient_form_energy V C b e he a c hx]
  have h := AdjointPointPair.CM.Construction.adjointChartPair_one_re V e he z hz b (a.val.inChart e (e x)) (c.val.inChart e (e x))
  simpa only [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair, z, ContinuousLinearEquiv.apply_symm_apply,
    GlobalLp.CM.Construction.varietyOneFormInChart] using h

theorem adjointL2Pair_zero_re (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 0 a c).re =
      inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V a) (GlobalLp.CM.Construction.varietySmoothScalarL2 V c) := by
  have h := integral_re (𝕜 := ℂ) (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V 0 a c)
  change (∫ x, (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 0 a.val c.val x).re
    ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) = (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 0 a c).re at h
  rw [← h, AdjointConjugation.CM.Construction.adjoint_metric_volume_eq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [GlobalLp.CM.Construction.varietySmoothScalarL2_coe V a, GlobalLp.CM.Construction.varietySmoothScalarL2_coe V c] with x hx hy
  rw [hx, hy]
  exact adjointPointPair_zero_re V a c x

theorem adjointL2Pair_one_re (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a c).re =
      ∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x (GlobalLp.CM.Construction.varietyOneFormField V C b a x))
        (GlobalLp.CM.Construction.varietyOneFormField V C b c x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  have h := integral_re (𝕜 := ℂ) (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V 1 a c)
  change (∫ x, (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 a.val c.val x).re
    ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) = (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a c).re at h
  rw [← h, AdjointConjugation.CM.Construction.adjoint_metric_volume_eq]
  exact integral_congr_ae (Filter.Eventually.of_forall (adjointPointPair_one_re V C b a c))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPair.CM.Construction
