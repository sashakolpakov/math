import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicTestDifferential

/-! # Scalar Test Pairing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarTestPairing.CM.Construction

noncomputable section

/-! The full complex degree-zero adjoint pairing has the actual scalar
chart-test formula and the same metric density as the one-form pairing. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem projectivePointPair_zero_scalar (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 0 a.val c.val x =
      star (HolomorphicPrimitive.CM.Construction.zeroFormScalar a x) * HolomorphicPrimitive.CM.Construction.zeroFormScalar c x := by
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  rw [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he x hx]
  change Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 0
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (e x) (e.map_source hx) 0 (a.val.inChart e (e x)))
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (e x) (e.map_source hx) 0 (c.val.inChart e (e x))) = _
  rw [ExteriorMetricLowDegree.CM.Construction.formMetricPair_zero]
  have hv (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (e x) (e.map_source hx) 0 (f.val.inChart e (e x)) 0 =
      HolomorphicPrimitive.CM.Construction.zeroFormScalar f x := by
    change f (e.symm (e x)) _ = f x 0
    rw [e.left_inv hx]
    exact congrArg (f x) (Subsingleton.elim _ _)
  rw [hv a, hv c]

theorem projectiveL2Pair_zero_scalar (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 0 a c =
      ∫ x, star (HolomorphicPrimitive.CM.Construction.zeroFormScalar a x) * HolomorphicPrimitive.CM.Construction.zeroFormScalar c x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (projectivePointPair_zero_scalar V a c)

theorem projectiveL2Pair_zero_chart_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 0 a (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg) =
      ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * star (ScalarChartLocalization.CM.Construction.varietyScalarChart V e a z) * g z := by
  let c := ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg
  have hc : ∀ x, x ∉ e.source → star (HolomorphicPrimitive.CM.Construction.zeroFormScalar a x) * HolomorphicPrimitive.CM.Construction.zeroFormScalar c x = 0 := by
    intro x hx
    have hzero : HolomorphicPrimitive.CM.Construction.zeroFormScalar c x = 0 := by
      change e.source.indicator (fun y => g ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e y))) x = 0
      exact Set.indicator_of_notMem hx _
    rw [hzero, mul_zero]
  rw [projectiveL2Pair_zero_scalar, Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => star (HolomorphicPrimitive.CM.Construction.zeroFormScalar a x) * HolomorphicPrimitive.CM.Construction.zeroFormScalar c x)
    (((Intersection.CM.Construction.zeroFormScalar_continuous a).star).mul (Intersection.CM.Construction.zeroFormScalar_continuous c)).aestronglyMeasurable hc]
  apply setIntegral_congr_fun (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
  intro z hz
  change (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
    (star (ScalarChartLocalization.CM.Construction.varietyScalarChart V e a z) * ScalarChartLocalization.CM.Construction.varietyScalarChart V e c z) = _
  rw [ChartTestFunction.CM.Construction.varietyChartTestForm_in_chart V e he g hgc hg hz]
  exact (mul_assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarTestPairing.CM.Construction
