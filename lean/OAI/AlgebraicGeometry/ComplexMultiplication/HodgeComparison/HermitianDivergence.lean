import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMatrixCalculus
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianMatrixPositive

/-! # Hermitian Divergence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianDivergence.CM.Construction

noncomputable section

/-! The determinant-weighted inverse of the actual projective Hermitian
metric has zero holomorphic divergence in every complex coordinate basis. -/

theorem varietyHermitian_weighted_inverse_divergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Module.Basis ι ℂ V.analyticModel)
    {y : V.analyticModel} (hy : y ∈ e.target) (k : ι) :
    ∑ i, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
      (fun z => (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v z).det * (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v z)⁻¹ i k)
      y (v i) = 0 := by
  apply HolomorphicMatrixCalculus.CM.Construction.holomorphic_weighted_inverse_divergence
    (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e v)
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_differentiableAt V e he v hy)
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_det_isUnit V e he v hy)
  intro i j l
  exact MetricDerivative.CM.Construction.varietyHermitian_holomorphic_derivative V e he hy (v i) (v j) (v l)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HermitianDivergence.CM.Construction
