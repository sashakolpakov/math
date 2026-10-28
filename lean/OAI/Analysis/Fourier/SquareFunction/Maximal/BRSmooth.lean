import OAI.Analysis.Fourier.SquareFunction.EuclideanKernel
import OAI.Analysis.Fourier.SquareFunction.SharpEnvelope
import OAI.Analysis.Fourier.BochnerRiesz.AnnularKernel
import OAI.Analysis.Fourier.BochnerRiesz.SmoothFactor

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

theorem enorm_convolution_le_maximal_envelope {n : ℕ} {a q C : ℝ}
    (ha : 0 < a) (hq : 0 < q) {K f : Space n → ℂ} {G : Space n → ℝ≥0∞}
    (hG : Measurable G) (hf : ∀ x, ‖f x‖ₑ ≤ G x)
    (hK : ∀ z, ‖K z‖ₑ ≤ ENNReal.ofReal C *
      (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * ‖z‖ + 1) ^ (-q)))) (x : Space n) :
    ‖OAI.Analysis.Fourier.WavePackets.complexConvolution K f volume x‖ₑ ≤
      ENNReal.ofReal C * (polynomialKernelMass n q * ballMaximal volume G x) := by
  have he : OAI.Analysis.Fourier.WavePackets.complexConvolution K f volume x = ∫ y, f y * K (x - y) := by
    unfold OAI.Analysis.Fourier.WavePackets.complexConvolution
    simpa only [sub_sub_cancel, mul_comm] using
      (integral_sub_left_eq_self (fun y : Space n => K y * f (x - y)) volume x).symm
  rw [he]
  calc
    _ ≤ ∫⁻ y, ‖f y * K (x - y)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal C * (G y *
        (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)))) := by
      apply lintegral_mono
      intro y
      change ‖f y • K (x - y)‖ₑ ≤ _
      rw [enorm_smul]
      apply (mul_le_mul' (hf y) (hK (x - y))).trans_eq
      rw [norm_sub_rev x y, ← dist_eq_norm]
      ac_rfl
    _ = ENNReal.ofReal C * (∫⁻ y, G y *
        (ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (normalized_polynomial_kernel_le_maximal ha hq hG x) _

theorem eLpNorm_ballMaximal_envelope_le {n : ℕ} {G : Space n → ℝ≥0∞}
    (hG : Measurable G) (ht : ∀ x, G x ≠ ⊤) {p : ℝ} (hp : 1 < p) :
    eLpNorm (ballMaximal volume G) (ENNReal.ofReal p) volume ≤
      (2 * ENNReal.ofReal ((5 : ℝ) ^ n * p / (p - 1)) ^ (1 / p)) *
        eLpNorm G (ENNReal.ofReal p) volume := by
  have h := eLpNorm_euclidean_ballMaximal_le hG.ennreal_toReal
    (fun x => ENNReal.toReal_nonneg) hp
  have he : (fun x => ENNReal.ofReal (G x).toReal) = G := by
    funext x
    exact ENNReal.ofReal_toReal (ht x)
  rw [he, eLpNorm_toReal_eq volume hG ht] at h
  exact h

/-- Every fixed smooth compact multiplier admits a uniform-in-dilation
pointwise maximal bound, including when its input is only dominated by an
extended-nonnegative measurable envelope. -/
theorem smooth_multiplier_maximal_envelope {n : ℕ} {a : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ B : ℝ, 0 < B ∧ ∀ h : ℝ, 0 < h → ∀ f : Space n → ℂ,
      ∀ G : Space n → ℝ≥0∞, Measurable G → (∀ x, ‖f x‖ₑ ≤ G x) → ∀ x,
      ‖OAI.Analysis.Fourier.WavePackets.complexConvolution (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => a (h • ξ))) f volume x‖ₑ ≤
        ENNReal.ofReal B * ballMaximal volume G x := by
  let q : ℝ := n + 1
  obtain ⟨C, hC, _, hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.angularInverse_kernel_decay ha hc q
  have hm : polynomialKernelMass n q ≠ ⊤ :=
    (polynomialKernelMass_lt_top (by dsimp [q]; linarith)).ne
  let B : ℝ := C * (polynomialKernelMass n q).toReal + 1
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro h hh f G hG hf x
  have hK (z : Space n) : ‖OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => a (h • ξ)) z‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal ((h⁻¹) ^ n) *
        ENNReal.ofReal ((h⁻¹ * ‖z‖ + 1) ^ (-q))) := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.angularInverse_dilate a hh, enorm_smul,
      Real.enorm_eq_ofReal (inv_nonneg.mpr (pow_nonneg hh.le n))]
    have hb := ENNReal.ofReal_le_ofReal (hbound (h⁻¹ • z)).1
    rw [ofReal_norm, ENNReal.ofReal_mul hC.le] at hb
    have H := mul_le_mul_right hb (ENNReal.ofReal ((h ^ n)⁻¹))
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh), inv_pow,
      mul_left_comm, mul_assoc] using H
  have H := enorm_convolution_le_maximal_envelope (inv_pos.mpr hh)
    (show 0 < q by dsimp [q]; positivity) hG hf hK x
  apply H.trans
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  calc
    ENNReal.ofReal C * polynomialKernelMass n q =
        ENNReal.ofReal (C * (polynomialKernelMass n q).toReal) := by
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hm]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by dsimp [B]; linarith)

theorem smooth_fourier_multiplier_maximal_envelope {n : ℕ} {a : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ B : ℝ, 0 < B ∧ ∀ h : ℝ, 0 < h → ∀ b : Space n → ℂ, Integrable b →
      ∀ G : Space n → ℝ≥0∞, Measurable G → (∀ x, ‖𝓕⁻ b x‖ₑ ≤ G x) → ∀ x,
      ‖𝓕⁻ (fun ξ => a (h • ((2 * Real.pi) • ξ)) * b ξ) x‖ₑ ≤
        ENNReal.ofReal B * ballMaximal volume G x := by
  obtain ⟨B, hB, hbound⟩ := smooth_multiplier_maximal_envelope ha hc
  refine ⟨B, hB, ?_⟩
  intro h hh b hb G hG hf x
  have ham : ContDiff ℝ ∞ (fun ξ : Space n => a (h • ((2 * Real.pi) • ξ))) := by fun_prop
  have hcm : HasCompactSupport (fun ξ : Space n => a (h • ((2 * Real.pi) • ξ))) :=
    (hc.comp_smul hh.ne').comp_smul (by positivity)
  rw [OAI.Analysis.Fourier.BochnerRiesz.fourierInv_mul_smooth_eq_convolution ham hcm hb]
  have he : (𝓕⁻ (fun ξ : Space n => a (h • ((2 * Real.pi) • ξ)))) =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => a (h • ξ)) := by
    funext y
    rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  rw [he]
  exact hbound h hh _ G hG hf x

end OAI.Analysis.Fourier.SquareFunction
