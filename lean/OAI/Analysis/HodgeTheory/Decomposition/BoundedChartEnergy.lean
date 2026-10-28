import OAI.Analysis.HodgeTheory.Decomposition.LocalEnergy
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzGradientSupport
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzEnergy
import OAI.Analysis.HodgeTheory.Decomposition.BoundedChartIntegrand
import OAI.Analysis.HodgeTheory.Decomposition.EnergyIntegration

/-! # Bounded Chart Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BoundedChartEnergy.Constructions

noncomputable section

/-! The bounded H¹ energy agrees with the actual Hodge coefficient
formula on compact chart tests wherever the extensions agree. -/

open _root_.MeasureTheory
open scoped SchwartzMap ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
  (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)

theorem projectiveLocalHodgeEnergy_schwartz
    (f g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hf : HasCompactSupport f) (hfs : tsupport f ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hηg : ∀ x ∈ tsupport g, η x = 1)
    (hAg : ∀ x ∈ tsupport g, A x = GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x) :
    let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
    let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
    LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB
      (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g) =
    ∫ x, inner ℝ (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x (p x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (f x)) (q x) +
      inner ℝ (GradientCoefficient.Constructions.projectiveHodgeValueCoefficient V e n x (LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he f hf hfs x)) (g x) := by
  dsimp only
  let p := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)
  let q := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 g)
  let Bf := ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU (f.toLp 2 volume)
  let Cp := ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU p
  let Ef := ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU (f.toLp 2 volume)
  rw [LocalEnergy.Constructions.projectiveLocalHodgeEnergy, VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz,
    VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz]
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB p q + inner ℝ Bf q +
    inner ℝ Cp (g.toLp 2 volume) + inner ℝ Ef (g.toLp 2 volume) = _
  exact (EnergyIntegration.Constructions.bounded_energy_three_pairs A hAm hAB p q Bf (g.toLp 2 volume) Cp Ef).trans
    (integral_congr_ae
      (BoundedChartIntegrand.Constructions.projectiveBoundedChartEnergy_integrand V e n he η hη hηc hηU A f g hf hfs hηg hAg))

end

end OAI.Analysis.HodgeTheory.Decomposition.BoundedChartEnergy.Constructions
