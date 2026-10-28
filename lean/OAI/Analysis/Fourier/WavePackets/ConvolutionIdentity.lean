import OAI.Analysis.Fourier.WavePackets.KernelIdentity
import OAI.Analysis.Fourier.LocalSmoothing.Definitions

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ContDiff RealInnerProductSpace

theorem scaled_wave_integral {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (X : EuclideanSpace ℝ (Fin n)) :
    (∫ ξ, oscillation (euclideanWavePhase X T) 1 ξ * φ (h • ξ)) =
      semiclassicalWaveKernel volume φ h T X := by
  have hp (ξ : EuclideanSpace ℝ (Fin n)) :
      oscillation (euclideanWavePhase X T) 1 ξ =
        oscillation (euclideanWavePhase X T) h (h • ξ) := by
    unfold oscillation euclideanWavePhase
    congr 2
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    field_simp
  simp_rw [hp]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun ξ => oscillation (euclideanWavePhase X T) h ξ * φ ξ) h (hR := hh.le)]
  simp only [semiclassicalWaveKernel, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem wave_phase_factorization {n : ℕ} (X Y ξ : EuclideanSpace ℝ (Fin n)) (T : ℝ) :
    Complex.exp (Complex.I * (⟪X, ξ⟫ : ℂ)) *
        (Complex.exp (-Complex.I * ((T * ‖ξ‖ : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * (⟪Y, ξ⟫ : ℂ))) =
      oscillation (euclideanWavePhase (X - Y) T) 1 ξ := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  unfold oscillation euclideanWavePhase
  congr 1
  simp only [inner_sub_left, div_one]
  push_cast
  ring

/-- Frequency localization makes the Fourier/convolution interchange absolutely
integrable for every `L¹` input, not just for Schwartz data. -/
theorem frequencyHalfWave_eq_integral_kernel {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (X : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun Y => semiclassicalWaveKernel volume φ h T (X - Y) * f Y) ∧
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f X =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        ∫ Y, semiclassicalWaveKernel volume φ h T (X - Y) * f Y := by
  let G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℂ := fun q =>
    oscillation (euclideanWavePhase (X - q.2) T) 1 q.1 * φ (h • q.1) * f q.2
  have hcut : Integrable (fun ξ => φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hs.comp_smul hh.ne')
  have hosc : Continuous (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      oscillation (euclideanWavePhase (X - q.2) T) 1 q.1) := by
    unfold oscillation euclideanWavePhase
    fun_prop
  have hG : Integrable G (volume.prod volume) := by
    apply (hcut.norm.mul_prod hf.norm).mono
      ((hosc.aestronglyMeasurable.mul hcut.aestronglyMeasurable.comp_fst).mul
        hf.aestronglyMeasurable.comp_snd)
    filter_upwards [] with q
    simp [norm_mul, norm_oscillation]
  have hinner (Y : EuclideanSpace ℝ (Fin n)) :
      (∫ ξ, G (ξ, Y)) = semiclassicalWaveKernel volume φ h T (X - Y) * f Y := by
    dsimp [G]
    rw [integral_mul_const, scaled_wave_integral φ hh]
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hG.integral_prod_right
  · unfold OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.angularInverse OAI.Analysis.Fourier.LocalSmoothing.angularFourier
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
    congr 1
    trans ∫ ξ, ∫ Y, G (ξ, Y)
    · apply integral_congr_ae
      filter_upwards [] with ξ
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with Y
      dsimp [G]
      rw [← wave_phase_factorization X Y ξ T]
      ring
    · rw [integral_integral_swap hG]
      apply integral_congr_ae
      filter_upwards [] with Y
      exact hinner Y

theorem frequencyHalfWave_eq_complexConvolution {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (X : EuclideanSpace ℝ (Fin n)) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f X = (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
      complexConvolution (semiclassicalWaveKernel volume φ h T) f volume X := by
  rw [(frequencyHalfWave_eq_integral_kernel hφ hs hh T hf X).2]
  congr 1
  simpa only [complexConvolution, sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun Y => semiclassicalWaveKernel volume φ h T (X - Y) * f Y) volume X).symm

end OAI.Analysis.Fourier.WavePackets
