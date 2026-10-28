import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PhaseIntegral
import Mathlib.MeasureTheory.Group.Integral

open _root_.MeasureTheory Set
open scoped ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- A fixed even nonnegative profile, supported sufficiently near zero that
its cosine transform stays positive throughout the observation annulus. -/
def kakeyaLogBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 32
  rOut := 1 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem kakeyaLogBump_integrable : Integrable (kakeyaLogBump : ℝ → ℝ) :=
  kakeyaLogBump.continuous.integrable_of_hasCompactSupport kakeyaLogBump.hasCompactSupport

theorem hasCompactSupport_complex_kakeyaLogBump :
    HasCompactSupport (fun u : ℝ ↦ (kakeyaLogBump u : ℂ)) := by
  apply kakeyaLogBump.hasCompactSupport.mono'
  intro u hu
  apply subset_tsupport (kakeyaLogBump : ℝ → ℝ)
  intro hz
  exact hu (by simp only [hz, Complex.ofReal_zero])

def kakeyaLogSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_complex_kakeyaLogBump.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp kakeyaLogBump.contDiff)

theorem kakeyaLogSchwartz_apply (u : ℝ) : kakeyaLogSchwartz u = (kakeyaLogBump u : ℂ) := rfl

theorem kakeyaLogBump_mass_pos : 0 < ∫ u, kakeyaLogBump u := by
  apply (integral_pos_iff_support_of_nonneg kakeyaLogBump.nonneg' kakeyaLogBump_integrable).mpr
  rw [kakeyaLogBump.support_eq]
  exact Metric.measure_ball_pos volume _ (by norm_num [kakeyaLogBump])

theorem kakeyaLogBump_support {u : ℝ} (hu : kakeyaLogBump u ≠ 0) : |u| < 1 / 16 := by
  have h : u ∈ Function.support (kakeyaLogBump : ℝ → ℝ) := hu
  rw [kakeyaLogBump.support_eq] at h
  simpa only [kakeyaLogBump, Metric.mem_ball, Real.dist_eq, sub_zero] using h

def kakeyaCosineProfile (s : ℝ) : ℝ := ∫ u, kakeyaLogBump u * Real.cos (s * u)

theorem kakeyaCosineProfile_integrable (s : ℝ) :
    Integrable (fun u ↦ kakeyaLogBump u * Real.cos (s * u)) :=
  (kakeyaLogBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
    kakeyaLogBump.hasCompactSupport.mul_right

theorem abs_kakeyaCosineProfile_le (s : ℝ) :
    |kakeyaCosineProfile s| ≤ ∫ u, kakeyaLogBump u := by
  change ‖∫ u, kakeyaLogBump u * Real.cos (s * u)‖ ≤ _
  apply norm_integral_le_of_norm_le kakeyaLogBump_integrable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg kakeyaLogBump.nonneg]
  exact mul_le_of_le_one_right kakeyaLogBump.nonneg (Real.abs_cos_le_one _)

theorem kakeyaCosineProfile_lower {s : ℝ} (hs : |s| ≤ 3) :
    (∫ u, kakeyaLogBump u) / 2 ≤ kakeyaCosineProfile s := by
  have hp (u : ℝ) : (1 / 2 : ℝ) * kakeyaLogBump u ≤ kakeyaLogBump u * Real.cos (s * u) := by
    by_cases hu : kakeyaLogBump u = 0
    · simp only [hu, mul_zero, zero_mul, le_refl]
    · have hub := kakeyaLogBump_support hu
      have hsmall : |s * u| ≤ 1 / 4 := by
        rw [abs_mul]
        nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg u)]
      have habs := abs_le.mp hsmall
      have hc := Real.one_sub_sq_div_two_le_cos (x := s * u)
      have hcos : (1 / 2 : ℝ) ≤ Real.cos (s * u) := by nlinarith
      simpa only [mul_comm (1 / 2 : ℝ)] using
        mul_le_mul_of_nonneg_left hcos kakeyaLogBump.nonneg
  have h := integral_mono (kakeyaLogBump_integrable.const_mul (1 / 2))
    (kakeyaCosineProfile_integrable s) hp
  rw [integral_const_mul] at h
  calc
    _ = (1 / 2 : ℝ) * ∫ u, kakeyaLogBump u := by ring
    _ ≤ _ := h

theorem kakeyaCosineProfile_lipschitz (s t : ℝ) :
    |kakeyaCosineProfile s - kakeyaCosineProfile t| ≤
      (∫ u, kakeyaLogBump u) * |s - t| := by
  rw [kakeyaCosineProfile, kakeyaCosineProfile,
    ← integral_sub (kakeyaCosineProfile_integrable s) (kakeyaCosineProfile_integrable t),
    ← integral_mul_const]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (kakeyaLogBump_integrable.mul_const _)
  filter_upwards [] with u
  rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg kakeyaLogBump.nonneg]
  by_cases hu : kakeyaLogBump u = 0
  · simp only [hu, zero_mul, le_refl]
  · have hub := kakeyaLogBump_support hu
    apply mul_le_mul_of_nonneg_left _ kakeyaLogBump.nonneg
    calc
      |Real.cos (s * u) - Real.cos (t * u)| ≤ |s * u - t * u| := Real.abs_cos_sub_cos_le _ _
      _ = |s - t| * |u| := by rw [← sub_mul, abs_mul]
      _ ≤ |s - t| := mul_le_of_le_one_right (abs_nonneg _) (by linarith)

theorem kakeyaLogBump_sine_integral (s : ℝ) :
    (∫ u, kakeyaLogBump u * Real.sin (s * u)) = 0 := by
  have h := integral_neg_eq_self
    (fun u : ℝ ↦ kakeyaLogBump u * Real.sin (s * u)) volume
  simp only [kakeyaLogBump.neg, mul_neg, Real.sin_neg, integral_neg] at h
  linarith

/-- Evenness removes the imaginary part of the Fourier profile exactly. -/
theorem radialProfile_kakeyaLogBump (s : ℝ) :
    OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (kakeyaLogBump : ℝ → ℝ) s = (kakeyaCosineProfile s : ℂ) := by
  have hi : Integrable (fun u : ℝ ↦
      Complex.exp (Complex.I * ((s * u : ℝ) : ℂ)) * (kakeyaLogBump u : ℂ)) := by
    simpa only [neg_neg, mul_one, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase] using
      OAI.Analysis.Fourier.LocalSmoothing.Sharpness.integrable_phase_weight kakeyaLogBump.continuous
        kakeyaLogBump.hasCompactSupport (-s) (K := fun _ ↦ (1 : ℂ)) continuous_const
  apply Complex.ext
  · change RCLike.re (∫ u : ℝ,
        Complex.exp (Complex.I * ((s * u : ℝ) : ℂ)) * (kakeyaLogBump u : ℂ)) = _
    rw [← integral_re hi]
    simp [Complex.exp_re, kakeyaCosineProfile, mul_comm]
  · change RCLike.im (∫ u : ℝ,
        Complex.exp (Complex.I * ((s * u : ℝ) : ℂ)) * (kakeyaLogBump u : ℂ)) = 0
    rw [← integral_im hi]
    simpa [Complex.exp_im, mul_comm] using kakeyaLogBump_sine_integral s

/-- The slowly varying real coefficient used in the thin-shell kernel. -/
def kakeyaLogWeight (n : ℕ) (T t : ℝ) : ℝ :=
  ((2 * Real.pi) ^ n)⁻¹ * kakeyaCosineProfile (t / T)

theorem abs_kakeyaLogWeight_le (n : ℕ) (T t : ℝ) :
    |kakeyaLogWeight n T t| ≤ ((2 * Real.pi) ^ n)⁻¹ * ∫ u, kakeyaLogBump u := by
  rw [kakeyaLogWeight, abs_mul, abs_of_pos (by positivity : 0 < ((2 * Real.pi) ^ n)⁻¹)]
  exact mul_le_mul_of_nonneg_left (abs_kakeyaCosineProfile_le _) (by positivity)

theorem kakeyaLogWeight_lower (n : ℕ) {T t : ℝ} (hT : 0 < T) (ht : |t| ≤ 3 * T) :
    ((2 * Real.pi) ^ n)⁻¹ * (∫ u, kakeyaLogBump u) / 2 ≤ kakeyaLogWeight n T t := by
  have hs : |t / T| ≤ 3 := by
    rw [abs_div, abs_of_pos hT]
    exact (div_le_iff₀ hT).mpr ht
  have h := mul_le_mul_of_nonneg_left (kakeyaCosineProfile_lower hs)
    (by positivity : 0 ≤ ((2 * Real.pi) ^ n)⁻¹)
  simpa only [mul_div_assoc, kakeyaLogWeight] using h

theorem kakeyaLogWeight_lipschitz (n : ℕ) {T : ℝ} (hT : 0 < T) (s t : ℝ) :
    |kakeyaLogWeight n T s - kakeyaLogWeight n T t| ≤
      (((2 * Real.pi) ^ n)⁻¹ * ∫ u, kakeyaLogBump u) / T * |s - t| := by
  rw [kakeyaLogWeight, kakeyaLogWeight, ← mul_sub, abs_mul,
    abs_of_pos (by positivity : 0 < ((2 * Real.pi) ^ n)⁻¹)]
  calc
    _ ≤ ((2 * Real.pi) ^ n)⁻¹ * ((∫ u, kakeyaLogBump u) * |s / T - t / T|) :=
      mul_le_mul_of_nonneg_left (kakeyaCosineProfile_lipschitz _ _) (by positivity)
    _ = _ := by rw [← sub_div, abs_div, abs_of_pos hT]; ring

end OAI.MeasureTheory.Kakeya
