import OAI.Analysis.Fourier.Wave.Continuity

open _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Fourier.Wave

/-- A Fourier multiplier on its natural L² domain; no boundedness of the
symbol is required. The domain condition is supplied explicitly. -/
def fourierMultiplierL2 {n : ℕ} (m : Space n → ℂ) (f : WaveL2 n)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2) :
    WaveL2 n :=
  (Lp.fourierTransformₗᵢ (Space n) ℂ).symm (hmf.toLp _)

/-- Plancherel for a multiplier on its natural domain, including unbounded
symbols such as the differentiated Bochner–Riesz multiplier. -/
theorem norm_sq_fourierMultiplierL2 {n : ℕ} (m : Space n → ℂ) (f : WaveL2 n)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2) :
    ‖fourierMultiplierL2 m f hmf‖ ^ 2 =
      ∫ ξ, ‖m ξ‖ ^ 2 * ‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2 := by
  unfold fourierMultiplierL2
  rw [LinearIsometryEquiv.norm_map, waveL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hmf.coeFn_toLp] with ξ hξ
  simp only [hξ, norm_mul, mul_pow]

theorem memLp_mul_bounded_symbol {n : ℕ} (m : Space n → ℂ)
    (hm : AEStronglyMeasurable m volume) (M : ℝ)
    (hM : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ M) (g : WaveL2 n) :
    MemLp (fun ξ ↦ m ξ * g ξ) 2 := by
  apply (Lp.memLp g).of_le_mul (c := M) (hm.mul (Lp.aestronglyMeasurable g))
  filter_upwards [hM] with ξ hξ
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hξ (norm_nonneg (g ξ))

theorem norm_fourierMultiplierL2_le {n : ℕ} (m : Space n → ℂ) (f : WaveL2 n)
    (hm : AEStronglyMeasurable m volume) (M : ℝ) (hM₀ : 0 ≤ M)
    (hM : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ M) :
    ‖fourierMultiplierL2 m f
      (memLp_mul_bounded_symbol m hm M hM ((Lp.fourierTransformₗᵢ (Space n) ℂ) f))‖
      ≤ M * ‖f‖ := by
  let g := (Lp.fourierTransformₗᵢ (Space n) ℂ) f
  have hb : ∀ᵐ ξ ∂volume, ‖m ξ * g ξ‖ ≤ M * ‖g ξ‖ := by
    filter_upwards [hM] with ξ hξ
    simpa only [norm_mul] using mul_le_mul_of_nonneg_right hξ (norm_nonneg (g ξ))
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (hm.mul (Lp.aestronglyMeasurable g)) hb 2
  unfold fourierMultiplierL2
  rw [LinearIsometryEquiv.norm_map, Lp.norm_toLp]
  have ht := ENNReal.toReal_mono (by finiteness) he
  simpa only [Pi.mul_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM₀, ← Lp.norm_def,
    g, LinearIsometryEquiv.norm_map] using ht

end OAI.Analysis.Fourier.Wave
