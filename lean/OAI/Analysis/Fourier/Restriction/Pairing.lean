import OAI.Analysis.Fourier.Restriction.Basic
import OAI.Analysis.Fourier.BochnerRiesz.DualityNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem angularFourier_star {n : ℕ} (f : Space n → ℂ) (ω : Space n) :
    star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x)) ω) =
      ∫ x, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * f x := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  change (starRingEnd ℂ) (∫ x, Complex.exp (-Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * star (f x)) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [← Complex.exp_conj]

/-- The actual angular-frequency restriction/extension pairing, including
absolute integrability of the double integral. -/
theorem integral_sphericalExtension_pairing {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    ∫ x, f x * OAI.Analysis.Fourier.Restriction.sphericalExtension g x =
      ∫ ω, g ω * star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x)) ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  have hi : Integrable (fun z : Space n × Space n ↦
      f z.1 * (Complex.exp (Complex.I * ((inner ℝ z.1 z.2 : ℝ) : ℂ)) * g z.2))
      (volume.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
    apply (hf.norm.mul_prod hg.norm).mono'
    · have hc : Continuous (fun z : Space n × Space n ↦
          Complex.exp (Complex.I * ((inner ℝ z.1 z.2 : ℝ) : ℂ))) := by fun_prop
      exact hf.aestronglyMeasurable.comp_fst.mul
        (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
    · filter_upwards [] with z
      simp only [norm_mul, norm_spherical_character, one_mul, le_refl]
  calc
    _ = ∫ x, ∫ ω, f x *
        (Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      simp only [OAI.Analysis.Fourier.Restriction.sphericalExtension, integral_const_mul]
    _ = ∫ ω, (∫ x, f x *
        (Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω)) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [angularFourier_star, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

end OAI.Analysis.Fourier.Restriction
