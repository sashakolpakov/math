import OAI.Analysis.Fourier.BochnerRiesz.DualBound
import OAI.Analysis.Fourier.BochnerRiesz.AnnularKernel
import OAI.Analysis.Fourier.BochnerRiesz.CompactInput
import OAI.Analysis.Fourier.Restriction.ConvolutionExpansion

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The bilinear pairing identity for an arbitrary smooth compact even
multiplier. No conjugation or reality condition on the symbol is needed. -/
theorem even_frequencyHalfWave_integral_pairing {n : ℕ} {m : Space n → ℂ}
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (heven : ∀ ξ, m (-ξ) = m ξ) (f g : SchwartzMap (Space n) ℂ) :
    (∫ x, g x * OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 f x) =
      ∫ x, f x * OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 g x := by
  rw [OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_fourierInv, OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_fourierInv]
  simp only [one_smul, ← SchwartzMap.fourier_coe]
  apply OAI.Analysis.Fourier.BochnerRiesz.even_multiplier_integral_pairing
    (fun ξ ↦ by rw [smul_neg, heven]) f g
  · exact OAI.Analysis.Fourier.BochnerRiesz.integrable_smooth_cycles_mul hm hmc (𝓕 f).integrable
  · exact OAI.Analysis.Fourier.BochnerRiesz.integrable_smooth_cycles_mul hm hmc (𝓕 g).integrable

/-- Transpose an even multiplier bound to the Holder-conjugate exponent,
retaining precisely the same constant. -/
theorem even_frequencyHalfWave_dual_bound {n : ℕ} {m : Space n → ℂ}
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (heven : ∀ ξ, m (-ξ) = m ξ) {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 g) (ENNReal.ofReal (p / (p - 1))) volume ≤
        C * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume)
    (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 f) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨D, _, hD⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_angularInverse_kernel_bound hm hmc
  have hfp : MemLp (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 f) (ENNReal.ofReal p) volume := by
    have H := (OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_frequencyHalfWave_zero_le hm.continuous hmc
      (by norm_num : (0 : ℝ) < 1) f.integrable hp1 ENNReal.ofReal_ne_top).trans
      (mul_le_mul' hD le_rfl)
    exact H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top)
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_schwartz_pairing hp hfp
  intro g
  rw [even_frequencyHalfWave_integral_pairing hm hmc heven f g]
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hgc : Continuous (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 g) := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_fourierInv]
    simp only [one_smul, ← SchwartzMap.fourier_coe]
    exact OAI.Analysis.Fourier.BochnerRiesz.continuous_fourierInv_of_integrable (OAI.Analysis.Fourier.BochnerRiesz.integrable_smooth_cycles_mul hm hmc (𝓕 g).integrable)
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 g) (ENNReal.ofReal (p / (p - 1))) volume :=
      OAI.Analysis.Fourier.BochnerRiesz.enorm_integral_mul_le_eLpNorm volume f.continuous.aestronglyMeasurable
        hgc.aestronglyMeasurable hpq
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume *
        (C * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) :=
      mul_le_mul' le_rfl (hbound g)
    _ = _ := by ring

theorem convolveKernel_angularInverse_eq_frequencyHalfWave {n : ℕ} {m : Space n → ℂ}
    (hm : Continuous m) (hmc : HasCompactSupport m) {f : Space n → ℂ}
    (hf : Integrable f) :
    OAI.Analysis.Fourier.SquareFunction.convolveKernel (OAI.Analysis.Fourier.LocalSmoothing.angularInverse m) f = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 f := by
  funext x
  rw [OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_convolution hm hmc (by norm_num) hf,
    OAI.Analysis.Fourier.SquareFunction.convolveKernel_commuted]
  simp only [one_smul, OAI.Analysis.Fourier.WavePackets.complexConvolution, smul_eq_mul, mul_comm]

/-- The transposed bound also holds on compactly supported `L¹ ∩ Lᵖ`
inputs, for the actual convolution kernel. -/
theorem even_multiplier_compact_convolution_bound {n : ℕ} {m : Space n → ℂ}
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (heven : ∀ ξ, m (-ξ) = m ξ) {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave m 1 0 g) (ENNReal.ofReal (p / (p - 1))) volume ≤
        C * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume)
    {f : Space n → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p) volume)
    {R : ℝ} (hR : 0 ≤ R) (hfs : ∀ x, R < ‖x‖ → f x = 0) :
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution (OAI.Analysis.Fourier.LocalSmoothing.angularInverse m) f) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨k, hk⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_schwartz_angularInverse hm hmc
  have hkc : Continuous (OAI.Analysis.Fourier.LocalSmoothing.angularInverse m) := by rw [← hk]; exact k.continuous
  have hkb : BddAbove (range fun x ↦ ‖OAI.Analysis.Fourier.LocalSmoothing.angularInverse m x‖) := by
    rw [← hk]
    exact ⟨SchwartzMap.seminorm ℝ 0 0 k, by
      rintro _ ⟨x, rfl⟩
      exact SchwartzMap.norm_le_seminorm ℝ k x⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have H := OAI.Analysis.Fourier.BochnerRiesz.convolution_bound_of_schwartz_compact hkc hkb hp1 ENNReal.ofReal_ne_top hC
    (fun g ↦ by
      rw [convolveKernel_angularInverse_eq_frequencyHalfWave hm.continuous hmc g.integrable]
      exact even_frequencyHalfWave_dual_bound hm hmc heven hp hbound g)
    hf hfp hR hfs
  convert H using 1
  unfold OAI.Analysis.Fourier.Restriction.sphericalKernelConvolution OAI.Analysis.Fourier.SquareFunction.convolveKernel
  simp only [smul_eq_mul, mul_comm]

end OAI.MeasureTheory.Kakeya
