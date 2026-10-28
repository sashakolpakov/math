import OAI.Analysis.Fourier.Restriction.KernelExpansion
import OAI.Analysis.Fourier.Restriction.Outgoing

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def radialConvolutionModel {n : ℕ} (A B : ℝ) (f : Space n → ℂ)
    (ω : Space n) (t : ℝ) : ℂ :=
  ∫ y, (radialOscillation A B (t - inner ℝ ω y) : ℝ) * f y

theorem integrable_radialConvolutionModel {n : ℕ} (A B t : ℝ) (ω : Space n)
    {f : Space n → ℂ} (hf : Integrable f) :
    Integrable (fun y ↦ (radialOscillation A B (t - inner ℝ ω y) : ℝ) * f y) := by
  apply hf.bdd_mul (c := |A| + |B|)
  · have hm : Continuous (fun y : Space n ↦
        ((radialOscillation A B (t - inner ℝ ω y) : ℝ) : ℂ)) := by
      dsimp [radialOscillation]
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [] with y
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_radialOscillation_le A B (t - inner ℝ ω y)

theorem radialConvolutionModel_outgoing {n : ℕ} (A B t : ℝ) (ω : Space n)
    {f : Space n → ℂ} (hf : Integrable f) :
    radialConvolutionModel A B f ω t - Complex.I *
      radialConvolutionModel A B f ω (t + Real.pi / 2) =
    ((A : ℂ) - Complex.I * (B : ℂ)) * Complex.exp (Complex.I * (t : ℂ)) *
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ω := by
  unfold radialConvolutionModel OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  rw [← integral_const_mul, ← integral_sub (integrable_radialConvolutionModel A B t ω hf)
    ((integrable_radialConvolutionModel A B (t + Real.pi / 2) ω hf).const_mul Complex.I),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  have he := radialOscillation_outgoing A B (t - inner ℝ ω y)
  rw [show t - inner ℝ ω y + Real.pi / 2 = t + Real.pi / 2 - inner ℝ ω y by ring] at he
  have hp : Complex.exp (Complex.I * ((t - inner ℝ ω y : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) *
        Complex.exp (-Complex.I * ((inner ℝ y ω : ℝ) : ℂ)) := by
    rw [real_inner_comm y ω, Complex.ofReal_sub, mul_sub, Complex.exp_sub]
    rw [div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    ring
  rw [hp] at he
  calc
    _ = (((radialOscillation A B (t - inner ℝ ω y) : ℝ) : ℂ) - Complex.I *
      (radialOscillation A B (t + Real.pi / 2 - inner ℝ ω y) : ℝ)) * f y := by ring
    _ = _ := by rw [he]; ring

def sphericalKernelConvolution {n : ℕ} (K f : Space n → ℂ) (x : Space n) : ℂ :=
  ∫ y, K (x - y) * f y

theorem integrable_sphericalKernelConvolution {n : ℕ} {K f : Space n → ℂ}
    (hKm : Measurable K) {M : ℝ} (hK : ∀ x, ‖K x‖ ≤ M)
    (hf : Integrable f) (x : Space n) : Integrable (fun y ↦ K (x - y) * f y) := by
  exact hf.bdd_mul ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y ↦ hK (x - y))

theorem convolution_radialModel_error {n : ℕ} {K f : Space n → ℂ}
    (hKm : Measurable K) {M : ℝ} (hK : ∀ x, ‖K x‖ ≤ M) (hf : Integrable f)
    (A B t P R E : ℝ) (ω : Space n) (_ : 0 ≤ E)
    (hfs : ∀ y, R < ‖y‖ → f y = 0)
    (herror : ∀ y, ‖y‖ ≤ R →
      ‖(P : ℂ) * K (t • ω - y) - (radialOscillation A B (t - inner ℝ ω y) : ℝ)‖ ≤ E) :
    ‖(P : ℂ) * sphericalKernelConvolution K f (t • ω) -
      radialConvolutionModel A B f ω t‖ ≤ E * ∫ y, ‖f y‖ := by
  let g := fun y : Space n ↦ ((P : ℂ) * K (t • ω - y) -
    (radialOscillation A B (t - inner ℝ ω y) : ℝ)) * f y
  have hg : Integrable g := by
    have H := ((integrable_sphericalKernelConvolution hKm hK hf (t • ω)).const_mul (P : ℂ)).sub
      (integrable_radialConvolutionModel A B t ω hf)
    convert H using 1
    funext y
    dsimp [g]
    ring
  have heq : (P : ℂ) * sphericalKernelConvolution K f (t • ω) -
      radialConvolutionModel A B f ω t = ∫ y, g y := by
    unfold sphericalKernelConvolution radialConvolutionModel
    rw [← integral_const_mul, ← integral_sub
      ((integrable_sphericalKernelConvolution hKm hK hf (t • ω)).const_mul (P : ℂ))
      (integrable_radialConvolutionModel A B t ω hf)]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [g]
    ring
  rw [heq, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hg.norm (hf.norm.const_mul E)
  intro y
  by_cases hy : ‖y‖ ≤ R
  · dsimp [g]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (herror y hy) (norm_nonneg _)
  · simp only [g, hfs y (lt_of_not_ge hy), mul_zero, norm_zero, le_refl]

end OAI.Analysis.Fourier.Restriction
