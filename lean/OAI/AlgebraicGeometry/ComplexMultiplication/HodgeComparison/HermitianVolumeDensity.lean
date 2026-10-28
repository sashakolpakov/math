import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealBasis
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointPointPair

/-! # Hermitian Volume Density -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction

noncomputable section

/-! The determinant of the projective Hermitian matrix is exactly the
Riemannian density used by the global Poisson solver. -/

def varietyEuclideanComplexBasis (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Module.Basis (Fin V.complexDimension) ℂ V.analyticModel :=
  (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ).toBasis.map
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toLinearEquiv

def euclideanToComplexMetricFiber (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V ≃L[ℂ]
      Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz :=
  (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).trans
    (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz).symm

theorem varietyMetricDensity_eq_hermitian_det (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) =
      (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (varietyEuclideanComplexBasis V)
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)).det := by
  rw [HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_eq_gram V e he _ hz]
  apply RealBasis.CM.Construction.metricDensity_eq_complex_gram
    (stdOrthonormalBasis ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ)
    (EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (euclideanToComplexMetricFiber V e he z hz).toContinuousLinearMap
  intro u v
  exact AdjointPointPair.CM.Construction.euclideanToMetricFiber_inner V e he z hz u v

theorem varietyNativeDensity_eq_hermitian_det (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) :
    (Metric.CM.Construction.varietyMetricDensity V e ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm y) : ℂ) =
      (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (varietyEuclideanComplexBasis V) y).det := by
  have hz : (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm y ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm y) ∈ e.target
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    varietyMetricDensity_eq_hermitian_det V e he hz

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction
