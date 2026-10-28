import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange

/-! # Adjoint Point Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPointPair.CM.Construction

noncomputable section

/-! The formal adjoint's pointwise metric in degrees zero and one agrees
with the scalar and inverse-metric pairings used by the Poisson solver. -/

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def varietyRealEuclideanCoordinates : EuclideanMetric.CM.Construction.varietyEuclideanModel V ≃L[ℝ] V.analyticModel where
  toLinearEquiv := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous
  continuous_invFun := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous

def euclideanToMetricFiber : EuclideanMetric.CM.Construction.varietyEuclideanModel V ≃L[ℝ]
    Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz :=
  (varietyRealEuclideanCoordinates V).trans
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveMetricFiberRealEquiv V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz).symm

theorem euclideanToMetricFiber_inner (u v : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z u v =
      inner ℝ (euclideanToMetricFiber V e he z hz u) (euclideanToMetricFiber V e he z hz v) := by
  rw [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveMetricFiber_real_inner, EuclideanMetric.CM.Construction.varietyEuclideanMetric_apply]
  let T := Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveMetricFiberRealEquiv V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz
  change KahlerDifferential.CM.Construction.varietyMetricInChart V e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v) =
    KahlerDifferential.CM.Construction.varietyMetricInChart V e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
      (T (T.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u))) (T (T.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V v)))
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

def metricFiberCovector (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) :
    Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz →L[ℝ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (F := ℂ) (0 : Fin 1)).symm
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 1 a)

theorem metricFiberCovector_pullback (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) :
    (metricFiberCovector V e he z hz a).comp (euclideanToMetricFiber V e he z hz).toContinuousLinearMap =
      OneFormFrameChange.CM.Construction.varietyCovectorOfFormValue V a := by
  apply ContinuousLinearMap.ext
  intro u
  let T := Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveMetricFiberRealEquiv V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz
  change a (fun _ => T (T.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u))) = a (fun _ => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u)
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem adjointChartPair_one_re {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) :
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 1 a c).re =
      inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator V e b z (GlobalLp.CM.Construction.varietyOneFormComponents V b a)) (GlobalLp.CM.Construction.varietyOneFormComponents V b c) := by
  change (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 1
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 1 a)
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 1 c)).re = _
  rw [ExteriorMetricLowDegree.CM.Construction.formMetricPair_one]
  change (Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (metricFiberCovector V e he z hz a).toLinearMap
    (metricFiberCovector V e he z hz c).toLinearMap).re = _
  rw [CovectorPair.CM.Construction.covectorInner_re_metric_pullback (EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz) (euclideanToMetricFiber V e he z hz)
    (euclideanToMetricFiber_inner V e he z hz), metricFiberCovector_pullback, metricFiberCovector_pullback]
  simp only [GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator, InverseMetric.CM.Construction.realBilinearOperator_apply, EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric,
    CovectorMetric.CM.Construction.complexGradientMetric_inverse_covectors, OneFormFrameChange.CM.Construction.varietyOneFormComponents_eq, GlobalLp.CM.Construction.complexCovectorSynthesis_components]

theorem adjointChartPair_zero_re (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 0) :
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 0 a c).re =
      inner ℝ (a 0) (c 0) := by
  change (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 0
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 0 a)
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 0 c)).re = _
  rw [ExteriorMetricLowDegree.CM.Construction.formMetricPair_zero]
  have hval (f : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 0) :
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz 0 f 0 = f 0 := by
    apply congrArg f
    exact Subsingleton.elim _ _
  rw [hval a, hval c, Complex.inner, Complex.star_def, mul_comm]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPointPair.CM.Construction
