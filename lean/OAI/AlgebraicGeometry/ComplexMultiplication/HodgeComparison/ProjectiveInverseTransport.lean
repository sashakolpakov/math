import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetricTransport

/-! # Projective Inverse Transport -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveInverseTransport.CM.Construction

noncomputable section

/-! The actual projective inverse Hermitian metric satisfies the raised
derivative symmetry in the fixed complex Euclidean chart coordinates. -/

open Filter
open scoped _root_.Topology ComplexOrder

theorem varietyEuclideanHermitian_holomorphic_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (i j k : Fin V.complexDimension) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w) j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w) j i) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k) := by
  have h₁ := MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_comp_complexLinear
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap
    (fun y => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) y j k)
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_differentiableAt V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz j k)
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i)
  have h₂ := MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_comp_complexLinear
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap
    (fun y => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) y j i)
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_differentiableAt V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz j i)
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k)
  exact h₁.trans ((MetricDerivative.CM.Construction.varietyHermitian_holomorphic_derivative V e he hz _ _ _).trans h₂.symm)

theorem varietyEuclideanHermitian_antiholomorphic_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (i j k : Fin V.complexDimension) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w) j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w) i k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
  let M := fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)
  have hs (a b : Fin V.complexDimension) : (fun w => M w a b) =ᶠ[𝓝 z]
      (fun w => star (M w b a)) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with w hw
    exact ((HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_posDef V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hw).isHermitian.apply a b).symm
  rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_congr (hs j k),
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_congr (hs i k),
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_star, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_star]
  exact congrArg (star : ℂ → ℂ) (varietyEuclideanHermitian_holomorphic_derivative V e he hz i k j)

theorem varietyEuclideanInverse_antiholomorphic_transport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (a j k : Fin V.complexDimension) :
    (∑ d, (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ a d *
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (fun w => (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) =
      ∑ d, (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ j d *
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (fun w => (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
          (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w))⁻¹ a k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d) := by
  let M := fun w => InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V w)
  have hM (r s : Fin V.complexDimension) : DifferentiableAt ℝ (fun w => M w r s) z :=
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_differentiableAt V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz r s).comp z
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).differentiableAt
  exact InverseMetricTransport.CM.Construction.antiholomorphic_inverse_transport_symmetric M hM
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_det_isUnit V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz)
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ)
    (varietyEuclideanHermitian_antiholomorphic_derivative V e he hz) a j k

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveInverseTransport.CM.Construction
