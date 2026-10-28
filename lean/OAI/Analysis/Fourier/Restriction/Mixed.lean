import OAI.Analysis.Fourier.Restriction.MixedNormalized

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sphericalExtension_congr_ae {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᵐ[OAI.Analysis.Fourier.Restriction.sphereMeasure n] g) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension f x = OAI.Analysis.Fourier.Restriction.sphericalExtension g x := by
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  simp only [hω]

theorem sphericalExtension_mixed_of_measurable {n : ℕ} {a s b : ℝ}
    (ha : 1 < a) (has : a ≤ s) (hb : 0 < b)
    (hab : a * (s - 1) / (a - 1) < b) {C : ℝ≥0∞}
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n → ℂ} (hgm : Measurable g)
    (hga : MemLp g (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal b) volume ≤
      mixedExtensionConstant n a s b C * eLpNorm g (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hap : 0 < a := by linarith
  have hpa : (1 : ℝ≥0∞) ≤ ENNReal.ofReal a := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha.le
  by_cases hzero : eLpNorm g (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) = 0
  · have hz := (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hap).ne').mp hzero
    have he : OAI.Analysis.Fourier.Restriction.sphericalExtension g = (fun _ ↦ 0) := by
      funext x
      rw [sphericalExtension_congr_ae hz x]
      simp [OAI.Analysis.Fourier.Restriction.sphericalExtension]
    simp [he, hzero]
  let N := eLpNorm g (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
  have hNt : N ≠ ⊤ := hga.eLpNorm_ne_top
  have hNz : N ≠ 0 := hzero
  have hNp : 0 < N.toReal := ENNReal.toReal_pos hNz hNt
  let c : ℂ := (N.toReal : ℂ)⁻¹
  have hNnorm : ‖(N.toReal : ℂ)‖ₑ = N := by
    rw [← ofReal_norm]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp] using
      ENNReal.ofReal_toReal hNt
  have hcnorm : ‖c‖ₑ = N⁻¹ := by
    change ‖(N.toReal : ℂ)⁻¹‖ₑ = N⁻¹
    rw [enorm_inv, hNnorm]
    exact_mod_cast hNp.ne'
  let g' : Space n → ℂ := c • g
  have hgm' : Measurable g' := hgm.const_smul c
  have hgi' : Integrable g' (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := (MemLp.integrable hpa hga).const_mul c
  have hgnorm : eLpNorm g' (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) = 1 := by
    rw [show g' = c • g from rfl, eLpNorm_const_smul, hcnorm]
    exact ENNReal.inv_mul_cancel hNz hNt
  have hgmoment : (∫⁻ ω, ‖g' ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ 1 := by
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hap hgm'.aestronglyMeasurable, hgnorm,
      ENNReal.one_rpow]
  have H := sphericalExtension_mixed_normalized ha has hb hab hdiag hgm' hgi' hgmoment
  have hrestore : g = (N.toReal : ℂ) • g' := by
    funext ω
    change g ω = (N.toReal : ℂ) * ((N.toReal : ℂ)⁻¹ * g ω)
    rw [← mul_assoc, mul_inv_cancel₀ (show (N.toReal : ℂ) ≠ 0 by exact_mod_cast hNp.ne'), one_mul]
  have hErestore : OAI.Analysis.Fourier.Restriction.sphericalExtension g = (N.toReal : ℂ) • OAI.Analysis.Fourier.Restriction.sphericalExtension g' := by
    funext x
    calc
      _ = OAI.Analysis.Fourier.Restriction.sphericalExtension ((N.toReal : ℂ) • g') x := congrArg (fun f ↦ OAI.Analysis.Fourier.Restriction.sphericalExtension f x) hrestore
      _ = _ := sphericalExtension_const_mul (N.toReal : ℂ) g' x
  rw [hErestore, eLpNorm_const_smul, hNnorm]
  calc
    _ ≤ N * mixedExtensionConstant n a s b C := by gcongr
    _ = _ := mul_comm _ _

/-- A diagonal spherical extension estimate implies the strict mixed estimate
above its interpolation line, for every input in the actual `Lᵃ` space. -/
theorem sphericalExtension_mixed {n : ℕ} {a s b : ℝ}
    (ha : 1 < a) (has : a ≤ s) (hb : 0 < b)
    (hab : a * (s - 1) / (a - 1) < b) {C : ℝ≥0∞}
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n → ℂ} (hga : MemLp g (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal b) volume ≤
      mixedExtensionConstant n a s b C * eLpNorm g (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  let g' := hga.aestronglyMeasurable.mk g
  have heq : g =ᵐ[OAI.Analysis.Fourier.Restriction.sphereMeasure n] g' := hga.aestronglyMeasurable.ae_eq_mk
  have hgm' : Measurable g' := hga.aestronglyMeasurable.measurable_mk
  have hga' : MemLp g' (ENNReal.ofReal a) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    rw [MemLp, ← eLpNorm_congr_ae heq]
    exact hga
  have H := sphericalExtension_mixed_of_measurable ha has hb hab hdiag hgm' hga'
  have hE : OAI.Analysis.Fourier.Restriction.sphericalExtension g = OAI.Analysis.Fourier.Restriction.sphericalExtension g' := funext (sphericalExtension_congr_ae heq)
  rwa [← hE, ← eLpNorm_congr_ae heq] at H

end OAI.Analysis.Fourier.Restriction
