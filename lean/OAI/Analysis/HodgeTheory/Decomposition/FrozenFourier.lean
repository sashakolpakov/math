import OAI.Analysis.HodgeTheory.Decomposition.FourierOperator
import OAI.Analysis.HodgeTheory.Decomposition.Symbol
import OAI.Analysis.HodgeTheory.Decomposition.PrincipalAdjoint

/-! # Frozen Fourier -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FrozenFourier.Constructions

noncomputable section

/-! Fourier formulas for the genuine exterior derivative and the metric
codifferential with coefficients frozen at a chart point. -/

open FourierTransform
open scoped SchwartzMap BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

theorem projectivePrincipalAdjointSymbol_basis
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol V e n he z hz ξ u =
      ∑ i, ξ (b i) • PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol V e n he z hz (b.coord i).toContinuousLinearMap u := by
  dsimp only
  let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  have hσ : SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ =
      ∑ i, ξ (b i) • SymbolEllipticity.Constructions.coordinateCovectorSymbol b n (b.coord i).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    simp only [sum_apply, smul_apply]
    exact Symbol.Constructions.coordinateCovectorSymbol_basis b n ξ a
  simp only [PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol_apply]
  change (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse
    ((SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ).adjoint (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z u)) = _
  rw [hσ]
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  rfl

def projectiveFrozenD :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) →L[ℂ]
      𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :=
  let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  FourierOperator.Constructions.schwartzFirstOrder b (fun i => ComplexMetric.Constructions.coordinateComplexSymbol b n (b.coord i).toContinuousLinearMap)

theorem projectiveFrozenD_fourier
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    𝓕 (projectiveFrozenD V n a) ξ = (2 * Real.pi * Complex.I) •
      ComplexMetric.Constructions.coordinateComplexSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (innerSL ℝ ξ) (𝓕 a ξ) := by
  rw [projectiveFrozenD, FourierOperator.Constructions.schwartzFirstOrder_fourier]
  congr 1
  exact (Symbol.Constructions.coordinateCovectorSymbol_basis (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (innerSL ℝ ξ) (𝓕 a ξ)).symm

def projectiveFrozenDelta (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) →L[ℂ]
      𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :=
  let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  Neg.neg (FourierOperator.Constructions.schwartzFirstOrder b (fun i => PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol V e n he z hz (b.coord i).toContinuousLinearMap))

theorem projectiveFrozenDelta_fourier (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    𝓕 (projectiveFrozenDelta V e n he z hz a) ξ = -(2 * Real.pi * Complex.I) •
      PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol V e n he z hz (innerSL ℝ ξ) (𝓕 a ξ) := by
  let b := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let S := fun i => PrincipalAdjoint.Constructions.projectivePrincipalAdjointSymbol V e n he z hz (b.coord i).toContinuousLinearMap
  change 𝓕 (-(FourierOperator.Constructions.schwartzFirstOrder b S a)) ξ = _
  rw [FourierTransform.fourier_neg]
  change -(𝓕 (FourierOperator.Constructions.schwartzFirstOrder b S a) ξ) = _
  rw [FourierOperator.Constructions.schwartzFirstOrder_fourier, neg_smul]
  exact congrArg (fun v => -((2 * Real.pi * Complex.I) • v))
    (projectivePrincipalAdjointSymbol_basis V e n he z hz (innerSL ℝ ξ) (𝓕 a ξ)).symm

end

end OAI.Analysis.HodgeTheory.Decomposition.FrozenFourier.Constructions
