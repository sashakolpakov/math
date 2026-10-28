import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferences
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds

/-! # Vector Difference Bounds -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceBounds.Constructions

noncomputable section

section

/-! Translation commutation and integration by parts for actual L2
difference quotients, including their Sobolev realizations. -/

open _root_.MeasureTheory FourierTransform

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem vectorL2Translation_zero (u : Lp F 2 (volume : Measure E)) : VectorTranslations.Constructions.vectorL2Translation (0 : E) u = u := by
  apply Lp.ext
  filter_upwards [VectorTranslations.Constructions.vectorL2Translation_coe (0 : E) u] with x hx
  simpa only [add_zero] using hx

omit [CompleteSpace F] in
theorem vectorL2Translation_add (m n : E) (u : Lp F 2 (volume : Measure E)) :
    VectorTranslations.Constructions.vectorL2Translation m (VectorTranslations.Constructions.vectorL2Translation n u) = VectorTranslations.Constructions.vectorL2Translation (m + n) u := by
  apply Lp.ext
  filter_upwards [VectorTranslations.Constructions.vectorL2Translation_coe m (VectorTranslations.Constructions.vectorL2Translation n u),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae (VectorTranslations.Constructions.vectorL2Translation_coe n u),
    VectorTranslations.Constructions.vectorL2Translation_coe (m + n) u] with x hm hn hmn
  rw [hm, hn, hmn, add_assoc]

omit [CompleteSpace F] in
theorem vectorL2Translation_inner (m : E) (u v : Lp F 2 (volume : Measure E)) :
    inner ℂ (VectorTranslations.Constructions.vectorL2Translation m u) v = inner ℂ u (VectorTranslations.Constructions.vectorL2Translation (-m) v) := by
  have h := (VectorTranslations.Constructions.vectorL2Translation m).inner_map_map u (VectorTranslations.Constructions.vectorL2Translation (-m) v)
  rw [vectorL2Translation_add, add_neg_cancel, vectorL2Translation_zero] at h
  exact h

omit [CompleteSpace F] in
/-- Discrete integration by parts for the genuine spatial difference quotient. -/
theorem vectorL2DifferenceQuotient_inner (m : E) (t : ℝ) (u v : Lp F 2 (volume : Measure E)) :
    inner ℂ (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u) v = -inner ℂ u (VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v) := by
  change inner ℂ ((t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u)) v =
    -inner ℂ u (((-t : ℝ) : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation ((-t) • m) v - v))
  rw [inner_smul_left, inner_sub_left, vectorL2Translation_inner, inner_smul_right, inner_sub_right]
  simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_neg, inv_neg, neg_smul]
  ring

theorem fourier_vectorL2Translation_coe (m : E) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (VectorTranslations.Constructions.vectorL2Translation m u) : Lp F 2 volume) x =
      (Real.fourierChar (inner ℝ m x) : ℂ) • (𝓕 u : Lp F 2 volume) x := by
  rw [VectorTranslations.Constructions.fourier_vectorL2Translation]
  exact VectorTranslations.Constructions.vectorL2TranslationPhase_coe m (𝓕 u)

/-- Every bounded temperate Fourier multiplier commutes with the actual
spatial translation. -/
theorem vectorL2Translation_multiplier_comm (m : E) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (u : Lp F 2 (volume : Measure E)) :
    VectorTranslations.Constructions.vectorL2Translation m (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier hg hC u) = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier hg hC (VectorTranslations.Constructions.vectorL2Translation m u) := by
  apply (Lp.fourierTransformₗᵢ E F).injective
  apply Lp.ext
  have hmult (v : Lp F 2 (volume : Measure E)) : ∀ᵐ x ∂(volume : Measure E),
      (𝓕 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier hg hC v) : Lp F 2 volume) x = g x • (𝓕 v : Lp F 2 volume) x :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn hg hC v _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier_distribution hg hC v)
  filter_upwards [fourier_vectorL2Translation_coe m (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier hg hC u),
    hmult u, hmult (VectorTranslations.Constructions.vectorL2Translation m u), fourier_vectorL2Translation_coe m u] with x htm hm hmt ht
  change (𝓕 (VectorTranslations.Constructions.vectorL2Translation m (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier hg hC u)) : Lp F 2 volume) x =
    (𝓕 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier hg hC (VectorTranslations.Constructions.vectorL2Translation m u)) : Lp F 2 volume) x
  rw [htm, hm, hmt, ht]
  simp only [smul_smul, mul_comm]

theorem vectorL2Translation_sobolevEmbedding_comm (m : E) {s : ℝ} (hs : 0 ≤ s)
    (u : Lp F 2 (volume : Measure E)) :
    VectorTranslations.Constructions.vectorL2Translation m (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs u) = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs (VectorTranslations.Constructions.vectorL2Translation m u) :=
  vectorL2Translation_multiplier_comm m (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.negative_besselSymbol_bound hs) u

theorem vectorL2Translation_sobolevDerivative_comm (m n : E) (u : Lp F 2 (volume : Measure E)) :
    VectorTranslations.Constructions.vectorL2Translation m (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n u) = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n (VectorTranslations.Constructions.vectorL2Translation m u) := by
  change VectorTranslations.Constructions.vectorL2Translation m ((2 * Real.pi * Complex.I : ℂ) •
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.normalizedDerivativeSymbol_bound n) u) = _
  rw [map_smul, vectorL2Translation_multiplier_comm]
  rfl

theorem vectorL2DifferenceQuotient_sobolevEmbedding_comm (m : E) (t : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (u : Lp F 2 (volume : Measure E)) :
    VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u) := by
  change (t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs u) - AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs u) =
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs ((t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u))
  rw [map_smul, map_sub, vectorL2Translation_sobolevEmbedding_comm]

theorem vectorL2DifferenceQuotient_sobolevDerivative_comm (m n : E) (t : ℝ)
    (u : Lp F 2 (volume : Measure E)) :
    VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u) := by
  change (t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n u) - AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n u) =
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative n ((t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u))
  rw [map_smul, map_sub, vectorL2Translation_sobolevDerivative_comm]

end

/-! Uniform vector-valued difference-quotient bounds from the genuine H¹ norm. -/

open _root_.MeasureTheory FourierTransform
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorL2DifferenceQuotient_sobolev_bound (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    ‖VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)‖ ≤
      (2 * Real.pi * ‖m‖) * ‖u‖ := by
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  have hJ : ∀ᵐ x ∂(volume : Measure E), (𝓕 (J u) : Lp F 2 volume) x =
      (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) • (𝓕 u : Lp F 2 volume) x :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.negative_besselSymbol_bound (by norm_num : (0 : ℝ) ≤ 1))
      u (J u) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution (by norm_num : (0 : ℝ) ≤ 1) u)
  change ‖VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (J u)‖ ≤ _
  rw [← Lp.norm_fourier_eq (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (J u)), ← Lp.norm_fourier_eq u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [VectorDifferences.Constructions.fourier_vectorL2DifferenceQuotient_coe m t (J u), hJ] with x hx hJx
  rw [hx, hJx, ← mul_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction.differenceQuotient_bessel_bound m x t) (norm_nonneg _)

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceBounds.Constructions
