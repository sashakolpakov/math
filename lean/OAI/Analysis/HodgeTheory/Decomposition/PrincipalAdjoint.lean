import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric
import OAI.Analysis.HodgeTheory.Decomposition.SymbolEllipticity

/-! # Principal Adjoint -/

namespace OAI.Analysis.HodgeTheory.Decomposition.PrincipalAdjoint.Constructions

noncomputable section

/-! The actual metric-adjoint principal symbol, bundled complex-linearly
for the Fourier estimate and compared with the proved real-coordinate energy. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

def projectiveComplexWeight (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℂ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  { toLinearMap :=
      { toFun := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        map_add' := (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).map_add
        map_smul' := ComplexMetric.Constructions.projectiveWeightedFormOperator_complex_smul V e n z }
    cont := (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).continuous }

def projectiveComplexInverseWeight (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℂ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  { toLinearMap :=
      { toFun := (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse
        map_add' := (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse.map_add
        map_smul' := ComplexMetric.Constructions.projectiveWeightedFormOperator_inverse_complex_smul V e n he z hz }
    cont := (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse.continuous }

def projectivePrincipalAdjointSymbol (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) →L[ℂ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  (projectiveComplexInverseWeight V e n he z hz).comp
    ((ComplexMetric.Constructions.coordinateComplexSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n ξ).adjoint.comp
      (projectiveComplexWeight V e (n + 1) z))

theorem projectivePrincipalAdjointSymbol_apply (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    projectivePrincipalAdjointSymbol V e n he z hz ξ u =
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse
        ((SymbolEllipticity.Constructions.coordinateCovectorSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n ξ).adjoint
          (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z u)) := by
  change (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse
    ((ComplexMetric.Constructions.coordinateComplexSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n ξ).adjoint.restrictScalars ℝ
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z u)) = _
  rw [← ComplexMetric.Constructions.euclidean_adjoint_restrictScalars, ComplexMetric.Constructions.coordinateComplexSymbol_restrictScalars]

/-- The Fourier-compatible principal symbols give exactly the actual metric Hodge energy. -/
theorem projectiveHodgeSymbolEnergy_complex (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) :
    SymbolEllipticity.Constructions.projectiveHodgeSymbolEnergy V e n (z, ξ, u) =
      (inner ℂ
        (projectiveComplexWeight V e (n + 1 + 1) z
          (ComplexMetric.Constructions.coordinateComplexSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1) ξ u))
        (ComplexMetric.Constructions.coordinateComplexSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1) ξ u)).re +
      (inner ℂ (projectiveComplexWeight V e n z (projectivePrincipalAdjointSymbol V e n he z hz ξ u))
        (projectivePrincipalAdjointSymbol V e n he z hz ξ u)).re := by
  rw [← CoordinateMetric.Constructions.euclidean_real_inner_eq_re, ← CoordinateMetric.Constructions.euclidean_real_inner_eq_re, projectivePrincipalAdjointSymbol_apply]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.PrincipalAdjoint.Constructions
