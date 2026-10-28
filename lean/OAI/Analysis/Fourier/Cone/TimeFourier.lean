import OAI.Analysis.Fourier.Cone.Measure
import OAI.Analysis.Fourier.SquareFunction.FourierL2
import OAI.Analysis.Fourier.Restriction.Interpolation

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.Cone

/-- Fourier synthesis on the unit radial interval, in angular frequency. -/
def coneTimeFourier (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ ρ, Complex.exp (Complex.I * ((t * ρ : ℝ) : ℂ)) * h ρ ∂coneRadialMeasure

theorem eLpNorm_fourier_unit_interval {h : ℝ → ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hh : MemLp h (ENNReal.ofReal p) coneRadialMeasure) :
    eLpNorm (𝓕 ((Icc (1 : ℝ) 2).indicator h)) (ENNReal.ofReal p) volume ≤
      eLpNorm h (ENNReal.ofReal p) coneRadialMeasure := by
  have hp0 : 0 < p := by linarith
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have h2 := hh.mono_exponent hp2
  have h1 := hh.integrable (by exact le_trans (by norm_num) hp2)
  let H := (Icc (1 : ℝ) 2).indicator h
  have H1 : Integrable H := (integrable_indicator_iff measurableSet_Icc).mpr h1
  have H2 : MemLp H 2 := (memLp_indicator_iff_restrict measurableSet_Icc).mpr h2
  have Hm : Continuous (𝓕 H) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr H1)]
    exact (Real.Lp.fourierTransform _).continuous
  have Hbound (t : ℝ) : ‖𝓕 H t‖ₑ ≤ eLpNorm H 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm H1.aestronglyMeasurable, Real.fourier_eq]
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    apply lintegral_congr
    intro x
    simp [← ofReal_norm]
  have H12 : eLpNorm H 1 volume ≤ eLpNorm h 2 coneRadialMeasure := by
    rw [show eLpNorm H 1 volume = eLpNorm h 1 coneRadialMeasure by
      exact eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
    have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := coneRadialMeasure)
      (f := h) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h2.aestronglyMeasurable
    simpa using he
  have H2p : eLpNorm h 2 coneRadialMeasure ≤ eLpNorm h (ENNReal.ofReal p) coneRadialMeasure := by
    have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := coneRadialMeasure)
      (f := h) hp2 hh.aestronglyMeasurable
    simpa using he
  have he := OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_enorm_bound volume Hm.aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 2) hp (Filter.Eventually.of_forall fun t => (Hbound t).trans H12)
  norm_num only [ENNReal.ofReal_ofNat] at he
  rw [OAI.Analysis.Fourier.SquareFunction.eLpNorm_fourier_line H1 H2,
    show eLpNorm H 2 volume = eLpNorm h 2 coneRadialMeasure by
      simpa only [H, coneRadialMeasure] using (eLpNorm_indicator_eq_eLpNorm_restrict
        (f := h) (p := (2 : ℝ≥0∞)) (μ := volume) measurableSet_Icc)] at he
  have hsum : (p - 2) / p + 2 / p = 1 := by field_simp; ring
  rw [← ENNReal.rpow_add_of_nonneg _ _ (div_nonneg (by linarith) hp0.le)
    (div_nonneg (by norm_num) hp0.le), hsum, ENNReal.rpow_one] at he
  exact he.trans H2p

theorem coneTimeFourier_eq_fourier (h : ℝ → ℂ) (t : ℝ) :
    coneTimeFourier h t = 𝓕 ((Icc (1 : ℝ) 2).indicator h) (-t / (2 * Real.pi)) := by
  rw [Real.fourier_eq']
  have hid : (fun ρ : ℝ => Complex.exp
      ((↑(-2 * Real.pi * inner ℝ ρ (-t / (2 * Real.pi)))) * Complex.I) •
        (Icc (1 : ℝ) 2).indicator h ρ) =
      (Icc (1 : ℝ) 2).indicator
        (fun ρ => Complex.exp (Complex.I * ((t * ρ : ℝ) : ℂ)) * h ρ) := by
    funext ρ
    have he : -2 * Real.pi * inner ℝ ρ (-t / (2 * Real.pi)) = t * ρ := by
      change -2 * Real.pi * ((-t / (2 * Real.pi)) * ρ) = t * ρ
      field_simp
    by_cases hρ : ρ ∈ Icc (1 : ℝ) 2
    · simp only [indicator_of_mem hρ, he, smul_eq_mul]
      rw [mul_comm Complex.I]
    · simp [hρ]
  rw [hid, integral_indicator measurableSet_Icc]
  rfl

theorem eLpNorm_real_mul (f : ℝ → ℂ) (p : ℝ≥0∞) {c : ℝ} (hc : c ≠ 0) :
    eLpNorm (fun t => f (c * t)) p volume =
      ENNReal.ofReal |c⁻¹| ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hm : MeasurableEmbedding (fun t : ℝ => c • t) :=
    (Homeomorph.mulLeft₀ c hc).measurableEmbedding
  have h := (hm.eLpNorm_map_measure (g := f) (p := p) (μ := volume)).symm
  rw [Measure.map_addHaar_smul volume hc,
    eLpNorm_smul_measure_of_ne_zero (by positivity)] at h
  simpa [Function.comp_def] using h

theorem eLpNorm_coneTimeFourier {h : ℝ → ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hh : MemLp h (ENNReal.ofReal p) coneRadialMeasure) :
    eLpNorm (coneTimeFourier h) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * Real.pi) ^ (1 / p) *
        eLpNorm h (ENNReal.ofReal p) coneRadialMeasure := by
  have hc : -(2 * Real.pi)⁻¹ ≠ 0 := neg_ne_zero.mpr
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have he : coneTimeFourier h = fun t =>
      𝓕 ((Icc (1 : ℝ) 2).indicator h) (-(2 * Real.pi)⁻¹ * t) := by
    funext t
    rw [coneTimeFourier_eq_fourier]
    ring_nf
  rw [he, eLpNorm_real_mul _ _ hc]
  have hs : |(-(2 * Real.pi)⁻¹)⁻¹| = 2 * Real.pi := by
    simp [abs_of_pos (show 0 < 2 * Real.pi by positivity)]
  rw [hs, ENNReal.toReal_ofReal (by linarith)]
  exact mul_le_mul' le_rfl (eLpNorm_fourier_unit_interval hp hh)

end OAI.Analysis.Fourier.Cone
