import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianDivergence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianVolumeDensity

/-! # Metric Coefficient Divergence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence.CM.Construction

noncomputable section

/-! Vanishing coefficient divergence with the actual Riemannian volume
density, in both native and Euclidean projective coordinates. -/

open Filter
open scoped _root_.Topology

theorem holomorphicDirectionalDerivative_congr {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative f x u = MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u := by
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, h.fderiv_eq]

theorem holomorphicDirectionalDerivative_comp_complexLinear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    (L : E →L[ℂ] F) (f : F → ℂ) {x : E} (hf : DifferentiableAt ℝ f (L x)) (u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => f (L y)) x u =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative f (L x) (L u) := by
  have hd := hf.hasFDerivAt.comp x (L.restrictScalars ℝ).hasFDerivAt
  change HasFDerivAt (fun y => f (L y)) ((fderiv ℝ f (L x)).comp (L.restrictScalars ℝ)) x at hd
  simp only [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, hd.fderiv, ContinuousLinearMap.comp_apply]
  change (1 / 2 : ℂ) * (fderiv ℝ f (L x) (L u) - Complex.I *
    fderiv ℝ f (L x) (L (Complex.I • u))) = _
  rw [map_smul]

theorem varietyNativeMetric_weighted_inverse_divergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {y : V.analyticModel} (hy : y ∈ e.target) (k : Fin V.complexDimension) :
    ∑ i, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
      (fun z => (Metric.CM.Construction.varietyMetricDensity V e ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm z) : ℂ) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) z)⁻¹ i k)
      y (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V i) = 0 := by
  have hi (i : Fin V.complexDimension) :
      (fun z => (Metric.CM.Construction.varietyMetricDensity V e ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm z) : ℂ) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) z)⁻¹ i k) =ᶠ[𝓝 y]
      (fun z => (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) z).det *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) z)⁻¹ i k) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    rw [HermitianVolumeDensity.CM.Construction.varietyNativeDensity_eq_hermitian_det V e he hz]
  simp_rw [holomorphicDirectionalDerivative_congr (hi _)]
  exact HermitianDivergence.CM.Construction.varietyHermitian_weighted_inverse_divergence V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hy k

theorem varietyEuclideanMetric_weighted_inverse_divergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (k : Fin V.complexDimension) :
    ∑ i, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
      (fun w => (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) *
        (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ i k)
      z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) = 0 := by
  let M := InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
  have hM := HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_differentiableAt V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz
  have hd := HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_det_isUnit V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz
  have hi (i : Fin V.complexDimension) :
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun w => (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) * (M (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ i k)
        z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => (M y).det * (M y)⁻¹ i k)
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V i) := by
    have hc : (fun w => (Metric.CM.Construction.varietyMetricDensity V e w : ℂ) * (M (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ i k) =ᶠ[𝓝 z]
        (fun w => (M (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)).det * (M (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ i k) := by
      filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with w hw
      rw [HermitianVolumeDensity.CM.Construction.varietyMetricDensity_eq_hermitian_det V e he hw]
    rw [holomorphicDirectionalDerivative_congr hc]
    exact holomorphicDirectionalDerivative_comp_complexLinear
      (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap
      (fun y => (M y).det * (M y)⁻¹ i k)
      ((HolomorphicMatrixCalculus.CM.Construction.matrix_determinant_differentiableAt M hM).mul (HolomorphicMatrixCalculus.CM.Construction.matrix_inverse_differentiableAt M hM hd i k)) _
  calc
    _ = ∑ i, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => (M y).det * (M y)⁻¹ i k)
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V i) :=
      Finset.sum_congr rfl (fun i _ => hi i)
    _ = 0 := HermitianDivergence.CM.Construction.varietyHermitian_weighted_inverse_divergence V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz k

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence.CM.Construction
