import OAI.Analysis.Fourier.Restriction.FourierProduct
import OAI.Analysis.Fourier.Restriction.Sparse.Kernel
import OAI.Analysis.Fourier.Restriction.Translations

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem angularFourier_mul_schwartz {n : ℕ} {f : Space n → ℂ}
    (hf : Integrable f) (u : SchwartzMap (Space n) ℂ) (ω : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f x * u x) ω =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∫ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier u (ω - ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  have H := angularFourier_mul_angularInverse hf (integrable_angularFourier_schwartz u) ω
  simp only [angularInverse_angularFourier_schwartz] at H
  rw [H]
  congr 1
  have he := integral_sub_left_eq_self
    (fun ξ : Space n ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ω - ξ)) volume ω
  simpa only [sub_sub_cancel] using he.symm

theorem localizedFourierKernel_reconstruction {n : ℕ} {f : Space n → ℂ}
    (hf : Integrable f) (u : SchwartzMap (Space n) ℂ) {R : ℝ} (hR : 0 < R)
    (z ω : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (x - z) * u (R⁻¹ • (x - z))) ω =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∫ ξ, localizedFourierKernel u R z ω ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  let v := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate R⁻¹ (inv_ne_zero hR.ne') u
  have hv (ξ : Space n) : OAI.Analysis.Fourier.LocalSmoothing.angularFourier v ξ =
      (R ^ n : ℝ) • OAI.Analysis.Fourier.LocalSmoothing.angularFourier u (R • ξ) := by
    change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ u (R⁻¹ • x)) ξ = _
    rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_dilate u (inv_pos.mpr hR)]
    simp only [inv_inv, inv_pow]
  have H := angularFourier_translate (fun x ↦ f x * v x) z ω
  change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (x - z) * u (R⁻¹ • (x - z))) ω = _ at H
  rw [H, angularFourier_mul_schwartz hf v]
  simp_rw [hv, localizedFourierKernel_eq u hR, Complex.real_smul]
  simp only [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

end OAI.Analysis.Fourier.Restriction
