import OAI.Analysis.Fourier.Restriction.RestrictedNormalized

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem restrictedFourierBound_interpolate_measurable {n : ℕ} {p r₀ r₁ : ℝ}
    (hp : 1 ≤ p) (hr₀ : 0 < r₀) (h₀p : r₀ < p) (hp₁ : p < r₁)
    {C₀ C₁ : ℝ≥0∞}
    (hres₀ : RestrictedFourierBound n r₀ (ENNReal.ofReal p) C₀)
    (hres₁ : RestrictedFourierBound n r₁ (ENNReal.ofReal p) C₁)
    {f : Space n → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (hfp : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      restrictedInterpolationConstant p r₀ r₁ C₀ C₁ * eLpNorm f (ENNReal.ofReal p) volume := by
  have hpp : 0 < p := by linarith
  by_cases hzero : eLpNorm f (ENNReal.ofReal p) volume = 0
  · have hz := (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hpp).ne').mp hzero
    have he : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f = (fun _ ↦ 0) := by
      funext ξ
      rw [angularFourier_congr_ae hz ξ]
      simp [OAI.Analysis.Fourier.LocalSmoothing.angularFourier]
    simp [he, hzero]
  let N := eLpNorm f (ENNReal.ofReal p) volume
  have hNt : N ≠ ⊤ := hfp.eLpNorm_ne_top
  have hNz : N ≠ 0 := hzero
  have hNp : 0 < N.toReal := ENNReal.toReal_pos hNz hNt
  let c : ℂ := (N.toReal : ℂ)⁻¹
  have hNnorm : ‖(N.toReal : ℂ)‖ₑ = N := by
    rw [← ofReal_norm]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp] using ENNReal.ofReal_toReal hNt
  have hcnorm : ‖c‖ₑ = N⁻¹ := by
    change ‖(N.toReal : ℂ)⁻¹‖ₑ = N⁻¹
    rw [enorm_inv, hNnorm]
    exact_mod_cast hNp.ne'
  let g : Space n → ℂ := c • f
  have hgm : Measurable g := hf.const_smul c
  have hgi : Integrable g := hfi.const_mul c
  have hgnorm : eLpNorm g (ENNReal.ofReal p) volume = 1 := by
    rw [show g = c • f from rfl, eLpNorm_const_smul, hcnorm]
    exact ENNReal.inv_mul_cancel hNz hNt
  have hgmoment : (∫⁻ x, ‖g x‖ₑ ^ p) ≤ 1 := by
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hpp hgm.aestronglyMeasurable, hgnorm, ENNReal.one_rpow]
  have H := restrictedFourierBound_normalized hp hr₀ h₀p hp₁ hres₀ hres₁ hgm hgi hgmoment
  have hrestore : f = (N.toReal : ℂ) • g := by
    funext x
    change f x = (N.toReal : ℂ) * ((N.toReal : ℂ)⁻¹ * f x)
    rw [← mul_assoc, mul_inv_cancel₀ (show (N.toReal : ℂ) ≠ 0 by exact_mod_cast hNp.ne'), one_mul]
  have hFrestore : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f = (N.toReal : ℂ) • OAI.Analysis.Fourier.LocalSmoothing.angularFourier g := by
    funext ξ
    calc
      _ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier ((N.toReal : ℂ) • g) ξ := congrArg (fun f ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) hrestore
      _ = _ := angularFourier_const_mul (N.toReal : ℂ) g ξ
  rw [hFrestore, eLpNorm_const_smul, hNnorm]
  calc
    _ ≤ N * restrictedInterpolationConstant p r₀ r₁ C₀ C₁ := by gcongr
    _ = _ := mul_comm _ _

/-- Interpolation of neighboring bounded-input estimates for the actual
Fourier restriction operator. No boundedness or support restriction remains. -/
theorem restrictedFourierBound_interpolate {n : ℕ} {p r₀ r₁ : ℝ}
    (hp : 1 ≤ p) (hr₀ : 0 < r₀) (h₀p : r₀ < p) (hp₁ : p < r₁)
    {C₀ C₁ : ℝ≥0∞}
    (hres₀ : RestrictedFourierBound n r₀ (ENNReal.ofReal p) C₀)
    (hres₁ : RestrictedFourierBound n r₁ (ENNReal.ofReal p) C₁)
    {f : Space n → ℂ} (hfi : Integrable f) (hfp : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      restrictedInterpolationConstant p r₀ r₁ C₀ C₁ * eLpNorm f (ENNReal.ofReal p) volume := by
  let g := hfi.aestronglyMeasurable.mk f
  have heq : f =ᵐ[volume] g := hfi.aestronglyMeasurable.ae_eq_mk
  have hgm : Measurable g := hfi.aestronglyMeasurable.measurable_mk
  have hgi : Integrable g := hfi.congr heq
  have hgp : MemLp g (ENNReal.ofReal p) volume := by
    rw [MemLp, ← eLpNorm_congr_ae heq]
    exact hfp
  have H := restrictedFourierBound_interpolate_measurable hp hr₀ h₀p hp₁ hres₀ hres₁ hgm hgi hgp
  have hF : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f = OAI.Analysis.Fourier.LocalSmoothing.angularFourier g := funext (angularFourier_congr_ae heq)
  rwa [← hF, ← eLpNorm_congr_ae heq] at H

end OAI.Analysis.Fourier.Restriction
