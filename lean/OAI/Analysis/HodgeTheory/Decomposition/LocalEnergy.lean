import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveLower
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFluxSobolev
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver

/-! # Local Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalEnergy.Constructions

noncomputable section

/-! A bounded local Hodge energy on genuine vector H¹ coordinates,
retaining every derived first-order and zeroth-order term. -/

open _root_.MeasureTheory
open scoped ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
  (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)

def projectiveLocalHodgeEnergy
    (u v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) : ℝ :=
  let D := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (D u) (D v) +
    inner ℝ (ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU (J u)) (D v) +
    inner ℝ (ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU (D u)) (J v) +
    inner ℝ (ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU (J u)) (J v)

theorem projectiveLocalHodgeEnergy_continuous_left
    (v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    Continuous (fun u => projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB u v) := by
  let D := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  apply Continuous.add
  · apply Continuous.add
    · apply Continuous.add
      · exact (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB).flip (D v)).continuous.comp D.continuous)
      · exact ((ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU).continuous.comp J.continuous).inner
          (𝕜 := ℝ) continuous_const
    · exact ((ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU).continuous.comp D.continuous).inner
        (𝕜 := ℝ) continuous_const
  · exact ((ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU).continuous.comp J.continuous).inner
      (𝕜 := ℝ) continuous_const

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalEnergy.Constructions
