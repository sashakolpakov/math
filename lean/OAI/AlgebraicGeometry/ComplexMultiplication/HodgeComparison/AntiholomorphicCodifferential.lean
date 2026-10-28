import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicCodifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation

/-! # Antiholomorphic Codifferential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicCodifferential.CM.Construction

noncomputable section

/-! Conjugation gives the actual antiholomorphic one-form codifferential
formula, with the inverse-Hermitian indices in their correct order. -/

open scoped ComplexOrder

theorem conjugateSmoothForm_antiholomorphic_is_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 0 1 a.val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 (Conjugation.CM.Construction.conjugateSmoothForm a).val := by
  intro e he y hy z v
  have h := congrArg (star : ℂ → ℂ) (ha e he y hy z v)
  change star (a.val.inChart e y (fun i => (z : ℂ) • v i)) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z * star (a.val.inChart e y v)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul, mul_one, star_mul, star_star, mul_comm] using h

theorem varietyOneFormComplexCoefficient_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (k : Fin V.complexDimension) :
    HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e (Conjugation.CM.Construction.conjugateSmoothForm a) k =
      fun z => star (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k z) := rfl

theorem varietyScalarChart_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Conjugation.CM.Construction.conjugateSmoothForm a) z = star (ScalarChartLocalization.CM.Construction.varietyScalarChart V e a z) := rfl

def varietyAntiholomorphicAdjointContraction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  ∑ j, ∑ k, (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ j k *
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a k) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)

theorem varietyHolomorphicAdjointContraction_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    star (HolomorphicCodifferential.CM.Construction.varietyHolomorphicAdjointContraction V e (Conjugation.CM.Construction.conjugateSmoothForm a) z) =
      varietyAntiholomorphicAdjointContraction V e a z := by
  simp only [HolomorphicCodifferential.CM.Construction.varietyHolomorphicAdjointContraction, varietyAntiholomorphicAdjointContraction, star_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [varietyOneFormComplexCoefficient_conjugate, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_star,
    star_mul, star_star,
    (HermitianMatrixPositive.CM.Construction.varietyHermitianMatrix_posDef V e he (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) hz).isHermitian.inv.apply j k,
    mul_comm]

theorem varietyAntiholomorphicCodifferential_formula (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 0 1 a.val)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ScalarChartLocalization.CM.Construction.varietyScalarChart V e (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0 a) z =
      -2 * varietyAntiholomorphicAdjointContraction V e a z := by
  have h := HolomorphicCodifferential.CM.Construction.varietyHolomorphicCodifferential_formula V e he (Conjugation.CM.Construction.conjugateSmoothForm a)
    (conjugateSmoothForm_antiholomorphic_is_holomorphic V a ha) hz
  rw [AdjointConjugation.CM.Construction.projectiveCodifferential_conjugate, varietyScalarChart_conjugate] at h
  have hs := congrArg (star : ℂ → ℂ) h
  rw [star_star, star_mul, star_neg, star_ofNat,
    varietyHolomorphicAdjointContraction_conjugate V e he a hz, mul_comm] at hs
  exact hs

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicCodifferential.CM.Construction
