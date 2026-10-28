import OAI.Analysis.Fourier.Restriction.FourierBump
import OAI.Analysis.Fourier.Restriction.WeightedKernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem integrable_angularFourier_schwartz {n : ℕ} (u : SchwartzMap (Space n) ℂ) :
    Integrable (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u) := by
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hFu : Integrable (⇑(𝓕 u : SchwartzMap (Space n) ℂ)) volume := (𝓕 u).integrable
  have H := hFu.comp_smul (inv_ne_zero hπ)
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularFourier u = fun ξ ↦ (𝓕 u : SchwartzMap (Space n) ℂ) ((2 * Real.pi)⁻¹ • ξ) := by
    funext ξ
    exact angularFourier_eq_scaled u ξ
  rwa [he]

theorem angularInverse_angularFourier_schwartz {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (x : Space n) : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u) x = u x := by
  rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  simp_rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  change 𝓕⁻ (𝓕 (u : Space n → ℂ)) x = u x
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe]
  rw [FourierTransform.fourierInv_fourier_eq]

theorem angularFourier_mul_angularInverse {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ω : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f x * OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x) ω =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        ∫ ξ, g ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ω - ξ) := by
  let F : Space n × Space n → ℂ := fun p ↦
    Complex.exp (-Complex.I * ((inner ℝ p.1 (ω - p.2) : ℝ) : ℂ)) * f p.1 * g p.2
  have hi : Integrable F (volume.prod volume) := by
    apply (hf.norm.mul_prod hg.norm).mono'
    · have hc : Continuous (fun p : Space n × Space n ↦
          Complex.exp (-Complex.I * ((inner ℝ p.1 (ω - p.2) : ℝ) : ℂ))) := by fun_prop
      exact (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_fst).mul
        hg.aestronglyMeasurable.comp_snd
    · filter_upwards [] with p
      simp [F, Complex.norm_exp]
  have hphase (x ξ : Space n) :
      Complex.exp (-Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((inner ℝ x (ω - ξ) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, inner_sub_right, Complex.ofReal_sub]
    congr 1
    ring
  calc
    _ = (((2 * Real.pi) ^ n)⁻¹ : ℝ) • ∫ x, ∫ ξ, F (x, ξ) := by
      unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, Complex.real_smul]
      simp only [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [F]
      rw [← hphase]
      ring
    _ = (((2 * Real.pi) ^ n)⁻¹ : ℝ) • ∫ ξ, ∫ x, F (x, ξ) := by
      rw [integral_integral_swap hi]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [F, OAI.Analysis.Fourier.LocalSmoothing.angularFourier]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

end OAI.Analysis.Fourier.Restriction
