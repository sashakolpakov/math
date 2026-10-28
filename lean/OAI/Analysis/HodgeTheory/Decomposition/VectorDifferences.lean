import OAI.Analysis.HodgeTheory.Decomposition.VectorTranslations
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients

/-! # Vector Differences -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorDifferences.Constructions

noncomputable section

/-! Actual vector-valued difference quotients and their Fourier symbols. -/

open _root_.MeasureTheory FourierTransform
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorL2DifferenceQuotient (m : E) (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  (t : ℂ)⁻¹ • ((VectorTranslations.Constructions.vectorL2Translation (t • m)).toContinuousLinearMap - ContinuousLinearMap.id ℂ _)

omit [CompleteSpace F] in
theorem vectorL2DifferenceQuotient_coe (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), vectorL2DifferenceQuotient m t u x =
      (t : ℂ)⁻¹ • (u (x + t • m) - u x) := by
  filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u),
    Lp.coeFn_sub (VectorTranslations.Constructions.vectorL2Translation (t • m) u) u, VectorTranslations.Constructions.vectorL2Translation_coe (t • m) u] with x hs hd ht
  change ((t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u) : Lp F 2 volume) x = _
  simp only [hs, hd, Pi.smul_apply, Pi.sub_apply, ht]

theorem fourier_vectorL2DifferenceQuotient_coe (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (vectorL2DifferenceQuotient m t u) : Lp F 2 volume) x =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) • (𝓕 u : Lp F 2 volume) x := by
  have heq : 𝓕 (vectorL2DifferenceQuotient m t u) =
      (t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2TranslationPhase (t • m) (𝓕 u) - 𝓕 u) := by
    change (Lp.fourierTransformₗᵢ E F) ((t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u)) = _
    rw [map_smul, map_sub]
    change (t : ℂ)⁻¹ • (𝓕 (VectorTranslations.Constructions.vectorL2Translation (t • m) u) - 𝓕 u) = _
    rw [VectorTranslations.Constructions.fourier_vectorL2Translation]
  rw [heq]
  filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (VectorTranslations.Constructions.vectorL2TranslationPhase (t • m) (𝓕 u) - 𝓕 u),
    Lp.coeFn_sub (VectorTranslations.Constructions.vectorL2TranslationPhase (t • m) (𝓕 u)) (𝓕 u),
    VectorTranslations.Constructions.vectorL2TranslationPhase_coe (t • m) (𝓕 u)] with x hs hd hp
  simp only [hs, hd, Pi.smul_apply, Pi.sub_apply, hp,
    real_inner_smul_left, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction.differenceQuotientSymbol]
  simp only [mul_smul, sub_smul, one_smul]

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorDifferences.Constructions
