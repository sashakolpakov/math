import OAI.Analysis.HodgeTheory.Decomposition.GradientCoefficient
import OAI.Analysis.HodgeTheory.Decomposition.HodgeFrozenGradient

/-! # Schwartz Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SchwartzEnergy.Constructions

noncomputable section

/-! The actual local Hodge energy on Schwartz form coefficients is exactly
the vector gradient energy with its derived lower-order terms. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

theorem projectiveLocalDelta_normalizedGradient
    (f : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hf : HasCompactSupport f) (hs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hs x =
        GradientRows.Constructions.normalizedGradientRow (fun i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x)
          (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
            (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x) + LocalCoefficientOperators.Constructions.projectiveAdjointZeroCoefficient V e n x (f x) := by
  filter_upwards [SchwartzGradientSupport.Constructions.normalizedGradientRow_schwartz (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (fun x i => LocalCoefficientOperators.Constructions.projectiveAdjointPrincipalCoefficient V e n i x) f] with x hx
  rw [LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz_apply, hx]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem projectiveHodge_schwartz_energy_expansion
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
    let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) x (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) f x))
        (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) g x) +
      inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n x (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x))
        (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he g hg hgs x) =
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x (p x)) (q x) +
        inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (f x)) (q x) +
        inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x
          (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x)) (g x) := by
  dsimp only
  filter_upwards [HodgeFrozenGradient.Constructions.projectiveFrozenD_normalizedGradient V n f,
    HodgeFrozenGradient.Constructions.projectiveFrozenD_normalizedGradient V n g,
    projectiveLocalDelta_normalizedGradient V e n he f hf hfs,
    projectiveLocalDelta_normalizedGradient V e n he g hg hgs] with x hdf hdg hδf hδg
  rw [← hdf, ← hdg, hδf, hδg]
  exact GradientCoefficient.Constructions.projectiveHodge_energy_expansion V e n x (f x) (g x) _ _

end

end OAI.Analysis.HodgeTheory.Decomposition.SchwartzEnergy.Constructions
