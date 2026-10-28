import OAI.Analysis.Fourier.Restriction.Pairing
import OAI.Analysis.Fourier.Restriction.FourierAmplitude
import OAI.Analysis.Fourier.Radial.Sphere.Decay

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem norm_angularFourier_le_integral_norm {n : ℕ} (f : Space n → ℂ) (ω : Space n) :
    ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω‖ ≤ ∫ y, ‖f y‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [norm_mul, Complex.norm_exp]
  simp

theorem integrable_angularFourier_sphere {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) :
    Integrable (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply (integrable_const (∫ y, ‖f y‖)).mono'
    (continuous_angularFourier hf).aestronglyMeasurable
  exact Eventually.of_forall (norm_angularFourier_le_integral_norm f)

theorem spherical_character_sub {n : ℕ} (x y ω : Space n) :
    Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((inner ℝ y ω : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((inner ℝ (x - y) ω : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, inner_sub_left]
  congr 1
  push_cast
  ring

/-- Multiplication by a Fourier transform on the sphere is convolution
against the corresponding spatial function. -/
theorem sphericalExtension_fourier_mul {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω * g ω) x =
      ∫ y, f y * OAI.Analysis.Fourier.Restriction.sphericalExtension g (x - y) := by
  let F : Space n × Space n → ℂ := fun z ↦ f z.1 *
    (Complex.exp (Complex.I * ((inner ℝ (x - z.1) z.2 : ℝ) : ℂ)) * g z.2)
  have hi : Integrable F (volume.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
    apply (hf.norm.mul_prod hg.norm).mono'
    · have hc : Continuous (fun z : Space n × Space n ↦
          Complex.exp (Complex.I * ((inner ℝ (x - z.1) z.2 : ℝ) : ℂ))) := by fun_prop
      exact hf.aestronglyMeasurable.comp_fst.mul
        (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
    · filter_upwards [] with z
      simp only [F, norm_mul, norm_spherical_character, one_mul, le_refl]
  calc
    _ = ∫ ω, ∫ y, F (y, ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply integral_congr_ae
      filter_upwards [] with ω
      unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
      rw [← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [F]
      rw [← spherical_character_sub]
      ring
    _ = ∫ y, ∫ ω, F (y, ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [F, OAI.Analysis.Fourier.Restriction.sphericalExtension, integral_const_mul]

end OAI.Analysis.Fourier.Restriction
