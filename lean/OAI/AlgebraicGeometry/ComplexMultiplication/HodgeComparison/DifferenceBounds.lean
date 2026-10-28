import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential

/-! # Difference Bounds -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction

noncomputable section

section

/-! Uniform difference-quotient bounds from the genuine H1 norm. -/

open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem differenceQuotient_bessel_bound (m x : E) (t : ℝ) :
    ‖DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) *
      (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ 2 * Real.pi * ‖m‖ := by
  rw [norm_mul]
  calc
    _ ≤ (2 * Real.pi * |inner ℝ m x|) * ‖(((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (DifferenceQuotients.CM.Construction.differenceQuotientSymbol_bound t _) (norm_nonneg _)
    _ = (2 * Real.pi) * ‖Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))‖ := by
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        real_inner_comm m x]
      ring
    _ ≤ 2 * Real.pi * ‖m‖ :=
      mul_le_mul_of_nonneg_left (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m x) (by positivity)

/-- Spatial difference quotients of an actual H1 function have a bound
independent of the translation size, in canonical Bessel coordinates. -/
theorem l2DifferenceQuotient_sobolev_bound (m : E) (t : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)‖ ≤
      (2 * Real.pi * ‖m‖) * ‖u‖ := by
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  have hJ : ∀ᵐ x ∂(volume : Measure E), (𝓕 (J u) : Lp ℂ 2 volume) x =
      (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * (𝓕 u : Lp ℂ 2 volume) x :=
    LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (by fun_prop) (SobolevIs.CM.Construction.negative_besselSymbol_bound (by norm_num : (0 : ℝ) ≤ 1))
      u (J u) (SobolevIs.CM.Construction.sobolevL2Embedding_distribution (by norm_num : (0 : ℝ) ≤ 1) u)
  change ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (J u)‖ ≤ _
  rw [← Lp.norm_fourier_eq (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (J u)), ← Lp.norm_fourier_eq u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [DifferenceQuotients.CM.Construction.fourier_l2DifferenceQuotient_coe m t (J u), hJ] with x hx hJx
  rw [hx, hJx, ← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_right (differenceQuotient_bessel_bound m x t) (norm_nonneg _)

theorem l2DifferenceQuotient_supported_bound (m : E) (t : ℝ) (K : Set E)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) :
    ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (SobolevIs.CM.Construction.supportedH1Embedding K u)‖ ≤ (2 * Real.pi * ‖m‖) * ‖u‖ :=
  l2DifferenceQuotient_sobolev_bound m t u.val

end

/-! Translation commutation and integration by parts for actual L2
difference quotients, including their Sobolev realizations. -/

open _root_.MeasureTheory FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem l2Translation_zero (u : Lp ℂ 2 (volume : Measure E)) : Translations.CM.Construction.l2Translation (0 : E) u = u := by
  apply Lp.ext
  filter_upwards [Translations.CM.Construction.l2Translation_coe (0 : E) u] with x hx
  simpa only [add_zero] using hx

theorem l2Translation_add (m n : E) (u : Lp ℂ 2 (volume : Measure E)) :
    Translations.CM.Construction.l2Translation m (Translations.CM.Construction.l2Translation n u) = Translations.CM.Construction.l2Translation (m + n) u := by
  apply Lp.ext
  filter_upwards [Translations.CM.Construction.l2Translation_coe m (Translations.CM.Construction.l2Translation n u),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae (Translations.CM.Construction.l2Translation_coe n u),
    Translations.CM.Construction.l2Translation_coe (m + n) u] with x hm hn hmn
  rw [hm, hn, hmn, add_assoc]

theorem l2Translation_inner (m : E) (u v : Lp ℂ 2 (volume : Measure E)) :
    inner ℂ (Translations.CM.Construction.l2Translation m u) v = inner ℂ u (Translations.CM.Construction.l2Translation (-m) v) := by
  have h := (Translations.CM.Construction.l2Translation m).inner_map_map u (Translations.CM.Construction.l2Translation (-m) v)
  rw [l2Translation_add, add_neg_cancel, l2Translation_zero] at h
  exact h

/-- Discrete integration by parts for the genuine spatial difference quotient. -/
theorem l2DifferenceQuotient_inner (m : E) (t : ℝ) (u v : Lp ℂ 2 (volume : Measure E)) :
    inner ℂ (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) v = -inner ℂ u (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v) := by
  change inner ℂ ((t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) u - u)) v =
    -inner ℂ u (((-t : ℝ) : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation ((-t) • m) v - v))
  rw [inner_smul_left, inner_sub_left, l2Translation_inner, inner_smul_right, inner_sub_right]
  simp only [map_inv₀, Complex.conj_ofReal, Complex.ofReal_neg, inv_neg, neg_smul]
  ring

theorem fourier_l2Translation_coe (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (Translations.CM.Construction.l2Translation m u) : Lp ℂ 2 volume) x =
      (Real.fourierChar (inner ℝ m x) : ℂ) * (𝓕 u : Lp ℂ 2 volume) x := by
  rw [Translations.CM.Construction.fourier_l2Translation]
  exact Translations.CM.Construction.l2TranslationPhase_coe m (𝓕 u)

/-- Every bounded temperate Fourier multiplier commutes with the actual
spatial translation. -/
theorem l2Translation_multiplier_comm (m : E) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (u : Lp ℂ 2 (volume : Measure E)) :
    Translations.CM.Construction.l2Translation m (SobolevIs.CM.Construction.l2FourierMultiplier hg hC u) = SobolevIs.CM.Construction.l2FourierMultiplier hg hC (Translations.CM.Construction.l2Translation m u) := by
  apply (Lp.fourierTransformₗᵢ E ℂ).injective
  apply Lp.ext
  have hmult (v : Lp ℂ 2 (volume : Measure E)) : ∀ᵐ x ∂(volume : Measure E),
      (𝓕 (SobolevIs.CM.Construction.l2FourierMultiplier hg hC v) : Lp ℂ 2 volume) x = g x * (𝓕 v : Lp ℂ 2 volume) x :=
    LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn hg hC v _ (SobolevIs.CM.Construction.l2FourierMultiplier_distribution hg hC v)
  filter_upwards [fourier_l2Translation_coe m (SobolevIs.CM.Construction.l2FourierMultiplier hg hC u),
    hmult u, hmult (Translations.CM.Construction.l2Translation m u), fourier_l2Translation_coe m u] with x htm hm hmt ht
  change (𝓕 (Translations.CM.Construction.l2Translation m (SobolevIs.CM.Construction.l2FourierMultiplier hg hC u)) : Lp ℂ 2 volume) x =
    (𝓕 (SobolevIs.CM.Construction.l2FourierMultiplier hg hC (Translations.CM.Construction.l2Translation m u)) : Lp ℂ 2 volume) x
  rw [htm, hm, hmt, ht]
  ring

theorem l2Translation_sobolevEmbedding_comm (m : E) {s : ℝ} (hs : 0 ≤ s)
    (u : Lp ℂ 2 (volume : Measure E)) :
    Translations.CM.Construction.l2Translation m (SobolevIs.CM.Construction.sobolevL2Embedding hs u) = SobolevIs.CM.Construction.sobolevL2Embedding hs (Translations.CM.Construction.l2Translation m u) :=
  l2Translation_multiplier_comm m (by fun_prop) (SobolevIs.CM.Construction.negative_besselSymbol_bound hs) u

theorem l2Translation_sobolevDerivative_comm (m n : E) (u : Lp ℂ 2 (volume : Measure E)) :
    Translations.CM.Construction.l2Translation m (SobolevDifferential.CM.Construction.sobolevL2Derivative n u) = SobolevDifferential.CM.Construction.sobolevL2Derivative n (Translations.CM.Construction.l2Translation m u) := by
  change Translations.CM.Construction.l2Translation m ((2 * Real.pi * Complex.I : ℂ) •
    SobolevIs.CM.Construction.l2FourierMultiplier (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound n) u) = _
  rw [map_smul, l2Translation_multiplier_comm]
  rfl

theorem l2DifferenceQuotient_sobolevEmbedding_comm (m : E) (t : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (u : Lp ℂ 2 (volume : Measure E)) :
    DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (SobolevIs.CM.Construction.sobolevL2Embedding hs u) =
      SobolevIs.CM.Construction.sobolevL2Embedding hs (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) := by
  change (t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) (SobolevIs.CM.Construction.sobolevL2Embedding hs u) - SobolevIs.CM.Construction.sobolevL2Embedding hs u) =
    SobolevIs.CM.Construction.sobolevL2Embedding hs ((t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) u - u))
  rw [map_smul, map_sub, l2Translation_sobolevEmbedding_comm]

theorem l2DifferenceQuotient_sobolevDerivative_comm (m n : E) (t : ℝ)
    (u : Lp ℂ 2 (volume : Measure E)) :
    DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (SobolevDifferential.CM.Construction.sobolevL2Derivative n u) =
      SobolevDifferential.CM.Construction.sobolevL2Derivative n (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) := by
  change (t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) (SobolevDifferential.CM.Construction.sobolevL2Derivative n u) - SobolevDifferential.CM.Construction.sobolevL2Derivative n u) =
    SobolevDifferential.CM.Construction.sobolevL2Derivative n ((t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) u - u))
  rw [map_smul, map_sub, l2Translation_sobolevDerivative_comm]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction
