import OAI.Analysis.Fourier.WavePackets.Half.Wave.AnnularKernel

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal RealInnerProductSpace

/-- Exact identification of the kernel with the normalization used in
the actual half-wave convolution formula. -/
theorem normalized_semiclassicalWaveKernel_eq_angularInverse {n : ℕ}
    (φ : Space n → ℂ) {h : ℝ} (hh : 0 < h) (T : ℝ) (x : Space n) :
    (((2*Real.pi : ℝ) : ℂ)^n)⁻¹*semiclassicalWaveKernel volume φ h T x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => waveAmplitude φ h T (h • ξ)) x := by
  rw [← scaled_wave_integral φ hh T x]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hphase : (T/h)*(h*‖ξ‖) = T*‖ξ‖ := by field_simp
  simp only [waveAmplitude,norm_smul,Real.norm_eq_abs,abs_of_pos hh,hphase]
  rw [← mul_assoc,← Complex.exp_add]
  unfold oscillation euclideanWavePhase
  congr 2
  push_cast
  ring

theorem eLpNorm_normalized_semiclassicalWaveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (T : ℝ) :
    eLpNorm (fun x => (((2*Real.pi : ℝ) : ℂ)^n)⁻¹*semiclassicalWaveKernel volume φ h T x)
      1 volume = eLpNorm (𝓕⁻ (waveAmplitude φ h T)) 1 volume := by
  have he := funext (normalized_semiclassicalWaveKernel_eq_angularInverse φ hh T)
  rw [he,OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_angularInverse_dilate_one (waveAmplitude_integrable hφ hc h T) hh,
    eLpNorm_fourierInv_eq_angularInverse (waveAmplitude_integrable hφ hc h T)]

/-- Uniform sharp L¹ bound for the actual normalized half-wave kernel.
It applies to arbitrary L¹ or bounded inputs through Young's inequality. -/
theorem uniform_semiclassicalWaveKernel_L1 {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (fun x => (((2*Real.pi : ℝ) : ℂ)^(d+1))⁻¹*
        semiclassicalWaveKernel volume φ h T x) 1 volume ≤ ENNReal.ofReal (C*h^(-(d : ℝ)/2)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_wave_annular_kernel hφ hc hz
  exact ⟨C,hC,fun h hh hh1 T hT =>
    (eLpNorm_normalized_semiclassicalWaveKernel hφ.continuous hc hh T).trans_le
      (hbound h hh hh1 T hT)⟩

end OAI.Analysis.Fourier.WavePackets
