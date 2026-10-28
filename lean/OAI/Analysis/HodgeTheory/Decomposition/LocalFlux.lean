import OAI.Analysis.HodgeTheory.Decomposition.LocalEnergy
import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Local Flux -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalFlux.Constructions

noncomputable section

/-! The actual bounded local Hodge energy yields a principal weak equation
with L² forcing and an H¹ lower-order flux. -/

open _root_.MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def projectiveLocalHodgeForcing
    (u f : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  f - ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU
      (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u) -
    ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)

def projectiveLocalHodgeFlux
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    Lp (GradientCoefficient.Constructions.ProjectiveGradientValues V n) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  -ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)

theorem projectiveLocalHodgeFlux_has_H1_coordinate
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ∃ w : Lp (GradientCoefficient.Constructions.ProjectiveGradientValues V n) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w =
        projectiveLocalHodgeFlux V e n he η hη hηc hηU u := by
  let Ju := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u
  have hJu : MemSobolev (1 : ℝ) 2
      (Ju : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :=
    VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_memSobolev (by norm_num : (0 : ℝ) ≤ 1) u
  have hJuNat : MemSobolev ((1 : ℕ) : ℝ) 2
      (Ju : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
    simpa only [Nat.cast_one] using hJu
  have hF : MemSobolev (1 : ℝ) 2
      (ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU Ju :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientCoefficient.Constructions.ProjectiveGradientValues V n)) := by
    simpa only [Nat.cast_one] using
      ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2_memSobolev V e n he η hη hηc hηU 1 Ju hJuNat
  obtain ⟨w, hw⟩ := (VectorEmbeddingRange.Constructions.vectorMemSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) _).mp hF
  refine ⟨-w, ?_⟩
  rw [map_neg, hw]
  rfl

theorem projectiveLocalHodgeEnergy_to_flux
    (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)
    (u v f : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hsol : LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB u v =
      inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v)) :
    let D := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
      (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (∫ x, inner ℝ (A x (D u x)) (D v x)) =
      inner ℝ (projectiveLocalHodgeForcing V e n he η hη hηc hηU u f)
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v) +
      inner ℝ (projectiveLocalHodgeFlux V e n he η hη hηc hηU u) (D v) := by
  dsimp only
  rw [LocalEnergy.Constructions.projectiveLocalHodgeEnergy, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply] at hsol
  rw [projectiveLocalHodgeForcing, projectiveLocalHodgeFlux,
    inner_sub_left, inner_sub_left, inner_neg_left]
  linarith only [hsol]

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalFlux.Constructions
