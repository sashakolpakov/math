import OAI.Analysis.Fourier.SquareFunction.KernelDilation

open OAI.Analysis.Fourier.Wave

/-! Dilation preserves the actual convolution operator norm, including on
non-Schwartz L¹∩Lᵖ inputs used in the localization argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem eLpNorm_dilate_any {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    (f : Space n → H) (p : ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun x => f (a • x)) p (volume : Measure (Space n)) =
      ENNReal.ofReal ((a ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hm : MeasurableEmbedding (fun x : Space n => a • x) :=
    (OAI.Analysis.Fourier.BochnerRiesz.realDilationEquiv n a ha.ne').toHomeomorph.measurableEmbedding
  have hh := (hm.eLpNorm_map_measure (g := f) (p := p) (μ := volume)).symm
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) ha.ne'] at hh
  simp only [Space, finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos ha n))] at hh
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at hh
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using hh

theorem dilation_norm_factor_cancel {n : ℕ} (p : ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal ((a ^ n)⁻¹) ^ (1 / p.toReal) *
      ENNReal.ofReal (((a⁻¹) ^ n)⁻¹) ^ (1 / p.toReal) = 1 := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p.toReal),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ha.le n)), inv_pow, inv_inv,
    inv_mul_cancel₀ (pow_ne_zero n ha.ne'), ENNReal.ofReal_one, ENNReal.one_rpow]

theorem convolve_dilatedKernel_bound {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (K : Space n → H) (f : Space n → ℂ) {p B : ℝ≥0∞}
    (hfi : Integrable f) (hfp : MemLp f p volume)
    (hB : ∀ (g : Space n → ℂ), Integrable g → MemLp g p volume →
      eLpNorm (convolveKernel K g) p volume ≤ B * eLpNorm g p volume)
    {a : ℝ} (ha : 0 < a) :
    eLpNorm (convolveKernel (dilatedKernel K a) f) p volume ≤ B * eLpNorm f p volume := by
  let g := fun x => f (a⁻¹ • x)
  have hgi : Integrable g := hfi.comp_smul (inv_ne_zero ha.ne')
  have hgp : MemLp g p volume := by
    change eLpNorm g p volume < ∞
    rw [show g = fun x => f (a⁻¹ • x) from rfl, eLpNorm_dilate_any f p (inv_pos.mpr ha)]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      hfp.eLpNorm_lt_top
  have he : convolveKernel (dilatedKernel K a) f = fun x => convolveKernel K g (a • x) :=
    funext (convolve_dilatedKernel K f ha)
  rw [he, eLpNorm_dilate_any _ p ha]
  calc
    _ ≤ ENNReal.ofReal ((a ^ n)⁻¹) ^ (1 / p.toReal) * (B * eLpNorm g p volume) :=
      mul_le_mul_right (hB g hgi hgp) _
    _ = B * eLpNorm f p volume := by
      rw [show g = fun x => f (a⁻¹ • x) from rfl, eLpNorm_dilate_any f p (inv_pos.mpr ha)]
      calc
        _ = (ENNReal.ofReal ((a ^ n)⁻¹) ^ (1 / p.toReal) *
            ENNReal.ofReal (((a⁻¹) ^ n)⁻¹) ^ (1 / p.toReal)) * (B * eLpNorm f p volume) := by ac_rfl
        _ = _ := by rw [dilation_norm_factor_cancel p ha, one_mul]

end OAI.Analysis.Fourier.SquareFunction
