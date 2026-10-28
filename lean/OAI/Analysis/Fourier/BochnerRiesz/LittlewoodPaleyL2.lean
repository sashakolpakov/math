import OAI.Analysis.Fourier.Wave.Multiplier
import OAI.Analysis.Fourier.BochnerRiesz.Projection

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Plancherel turns a finite pointwise square-symbol bound into an aggregate
operator bound, on the full natural L² domain. -/
theorem sum_norm_sq_fourierMultiplierL2_le {ι : Type*} {n : ℕ}
    (s : Finset ι) (m : ι → Space n → ℂ) (f : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hmf : ∀ i, MemLp (fun ξ ↦ m i ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ) 2)
    (M : ℝ) (hM : ∀ᵐ ξ ∂volume, ∑ i ∈ s, ‖m i ξ‖ ^ 2 ≤ M) :
    ∑ i ∈ s, ‖OAI.Analysis.Fourier.Wave.fourierMultiplierL2 (m i) f (hmf i)‖ ^ 2 ≤ M * ‖f‖ ^ 2 := by
  have hi (i : ι) : Integrable (fun ξ ↦
      ‖m i ξ‖ ^ 2 * ‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using (hmf i).norm.integrable_sq
  calc
    _ = ∫ ξ, ∑ i ∈ s, ‖m i ξ‖ ^ 2 * ‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2 := by
      rw [MeasureTheory.integral_finsetSum s (fun i _ ↦ hi i)]
      exact Finset.sum_congr rfl (fun i _ ↦ OAI.Analysis.Fourier.Wave.norm_sq_fourierMultiplierL2 (m i) f (hmf i))
    _ ≤ ∫ ξ, M * ‖((Lp.fourierTransformₗᵢ (Space n) ℂ) f) ξ‖ ^ 2 := by
      apply integral_mono_ae (MeasureTheory.integrable_finsetSum s (fun i _ ↦ hi i))
        ((Lp.memLp ((Lp.fourierTransformₗᵢ (Space n) ℂ) f)).norm.integrable_sq.const_mul M)
      filter_upwards [hM] with ξ hξ
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hξ (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul, ← OAI.Analysis.Fourier.Wave.waveL2_norm_sq_integral, LinearIsometryEquiv.norm_map]

end OAI.Analysis.Fourier.BochnerRiesz
