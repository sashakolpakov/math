import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric

/-! # Metric Jacobian -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricJacobian.CM.Construction

noncomputable section

/-! The actual metric volume density transforms by the absolute Jacobian. -/

open scoped ContDiff _root_.Manifold
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def pullbackBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E E ℝ).flip L).comp (B.comp L)

theorem pullbackBilinear_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) (u v : E) :
    pullbackBilinear B L u v = B (L u) (L v) := rfl

theorem metricMatrix_pullback (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    Metric.CM.Construction.metricMatrix b (pullbackBilinear B L) =
      (LinearMap.toMatrix b b L.toLinearMap).transpose * Metric.CM.Construction.metricMatrix b B *
        LinearMap.toMatrix b b L.toLinearMap := by
  have h : Metric.CM.Construction.bilinearUnderlying (pullbackBilinear B L) =
      (Metric.CM.Construction.bilinearUnderlying B).comp L.toLinearMap L.toLinearMap := rfl
  rw [Metric.CM.Construction.metricMatrix, h]
  exact LinearMap.BilinForm.toMatrix_comp b b _ _ _

theorem metricMatrix_det_pullback (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    (Metric.CM.Construction.metricMatrix b (pullbackBilinear B L)).det =
      (LinearMap.det L.toLinearMap) ^ 2 * (Metric.CM.Construction.metricMatrix b B).det := by
  rw [metricMatrix_pullback, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  ring

theorem metricDensity_pullback (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (L : E →L[ℝ] E) :
    Metric.CM.Construction.metricDensity b (pullbackBilinear B L) =
      |LinearMap.det L.toLinearMap| * Metric.CM.Construction.metricDensity b B := by
  unfold Metric.CM.Construction.metricDensity
  rw [metricMatrix_det_pullback, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

def varietyEuclideanTransition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanMetric.CM.Construction.varietyEuclideanModel V :=
  (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm ∘ (f ∘ e.symm) ∘ EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V

theorem varietyEuclideanTransition_hasFDerivAt (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hfz : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source) :
    HasFDerivAt (varietyEuclideanTransition V e f)
      (((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.toContinuousLinearMap.restrictScalars ℝ).comp
        ((fderiv ℝ (f ∘ e.symm) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)).comp
          ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ))) z := by
  have ht := (Analysis.DifferentialForms.Manifold.Charts.contDiffAt_chart_transition e f he hf hz hfz).differentiableAt (by simp)
  have hL : HasFDerivAt (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V)
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ) z :=
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  have hLi : HasFDerivAt (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.toContinuousLinearMap.restrictScalars ℝ)
      (f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) :=
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  exact hLi.comp z (ht.hasFDerivAt.comp z hL)

theorem varietyEuclideanMetric_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hfz : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source) :
    EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z =
      pullbackBilinear (EuclideanMetric.CM.Construction.varietyEuclideanMetric V f (varietyEuclideanTransition V e f z))
        (fderiv ℝ (varietyEuclideanTransition V e f) z) := by
  ext u v
  rw [pullbackBilinear_apply, EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply, EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply,
    (varietyEuclideanTransition_hasFDerivAt V e f he hf hz hfz).fderiv]
  simp only [varietyEuclideanTransition, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact KahlerDifferential.CM.Construction.varietyMetricInChart_transition V e f he hf hz hfz _ _

theorem varietyMetricDensity_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hfz : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source) :
    Metric.CM.Construction.varietyMetricDensity V e z =
      |LinearMap.det (fderiv ℝ (varietyEuclideanTransition V e f) z).toLinearMap| *
        Metric.CM.Construction.varietyMetricDensity V f (varietyEuclideanTransition V e f z) := by
  unfold Metric.CM.Construction.varietyMetricDensity
  rw [varietyEuclideanMetric_transition V e f he hf hz hfz, metricDensity_pullback]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricJacobian.CM.Construction
