import OAI.Analysis.PDE.WaveEquation.Trigonometric
import OAI.Analysis.PDE.WaveEquation.LowEstimate

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

theorem angularInverse_cosine_average {n : ℕ} {a : Space n → ℂ}
    (ha : Integrable a) (ham : Continuous a) (t : ℝ) (x : Space n) :
    (∫ s in Icc (0:ℝ) 1, OAI.Analysis.Fourier.LocalSmoothing.angularInverse
      (fun ξ ↦ (Real.cos ((t*‖ξ‖)*s) : ℂ) * a ξ) x) =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ (Real.sinc (t*‖ξ‖) : ℂ) * a ξ) x := by
  let ν : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
  let H : ℝ × Space n → ℂ := fun z ↦
    Complex.exp (Complex.I * (inner ℝ x z.2 : ℂ)) *
      ((Real.cos ((t*‖z.2‖)*z.1) : ℂ) * a z.2)
  have hH : Integrable H (ν.prod volume) := by
    apply ((integrable_const (1:ℝ) : Integrable (fun _ : ℝ ↦ (1:ℝ)) ν).mul_prod ha.norm).mono'
    · have hc : Continuous H := by dsimp only [H]; fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [] with z
      simp only [H,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Real.exp_zero,
        one_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  change (∫ s, ((2*Real.pi)^n)⁻¹ • (∫ ξ, H (s,ξ)) ∂ν) = _
  rw [integral_smul,integral_integral_swap hH]
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (∫ s, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
    ((Real.cos ((t*‖ξ‖)*s) : ℂ) * a ξ) ∂ν) = _
  rw [integral_const_mul,integral_mul_const]
  change Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
    ((∫ s in Icc (0:ℝ) 1, (Real.cos ((t*‖ξ‖)*s) : ℂ)) * a ξ) = _
  rw [integral_cosine_unit]

/-- The time-integrated compact-frequency cosine propagator is exactly
the removable sine-over-frequency multiplier, including the value at zero. -/
theorem frequencyWavePrimitive_eq_sinc {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (t : ℝ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyWavePrimitive χ t f x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ ((t * Real.sinc (t*‖ξ‖) : ℝ) : ℂ) *
        χ ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x := by
  let a : Space n → ℂ := fun ξ ↦ χ ξ * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ
  have ham : Continuous a := hχ.continuous.mul (OAI.Analysis.Fourier.Restriction.continuous_angularFourier f.integrable)
  have ha : Integrable a := ham.integrable_of_hasCompactSupport hc.mul_right
  have he (s : ℝ) : (1/2:ℝ) •
      (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (t*s) f x + OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 (-(t*s)) f x) =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ (Real.cos ((t*‖ξ‖)*s) : ℂ) * a ξ) x := by
    rw [frequencyCosine_eq_inverse hχ hc]
    congr 1
    funext ξ
    dsimp only [a]
    rw [show (t*s)*‖ξ‖ = (t*‖ξ‖)*s by ring]
    ring
  simp only [frequencyWavePrimitive,he]
  rw [angularInverse_cosine_average ha ham,← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_smul_real]
  congr 1
  funext ξ
  simp only [a,Complex.real_smul,Complex.ofReal_mul]
  ring

end OAI.Analysis.PDE.WaveEquation
