import OAI.Analysis.Fourier.BochnerRiesz.PositiveTime
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Exponents

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The frequency-localized critical estimate retains its logarithmic loss on
every positive time slab. -/
theorem logarithmic_annular_slab (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h r : ℝ, 0 < h → h ≤ r →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.BochnerRiesz.timeSlabMeasure n r) ≤
      ENNReal.ofReal (C * r ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) *
        (1 + Real.log (r / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨C, hC, hb⟩ := hlog n hn χ hχ hc hzero
  refine ⟨C, hC, ?_⟩
  intro h r hh hhr f hcut
  have hr : 0 < r := hh.trans_le hhr
  have hp : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n :=
    lt_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn)
  let g := OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate r hr.ne' f
  have hcutg : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ ≠ 0 → χ ((h / r) • ξ) = 1 := by
    intro ξ hξ
    have hnz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (r⁻¹ • ξ) ≠ 0 := by
      intro hz
      apply hξ
      change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (r • x)) ξ = 0
      rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_dilate f hr, hz, smul_zero]
    simpa only [smul_smul, div_eq_mul_inv] using hcut (r⁻¹ • ξ) hnz
  have heq : (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ (h / r) z.2 g z.1) =
      (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (r * z.2) f (r • z.1)) := by
    funext z
    rw [← OAI.Analysis.Fourier.BochnerRiesz.halfWaveIntegral_dilate f hr z.2 z.1]
    unfold OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral
    congr 1
    funext ξ
    have hgeq : (g : Space n → ℂ) = fun y ↦ f (r • y) := by
      funext y
      rfl
    rw [← hgeq]
    by_cases hz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ = 0
    · simp [hz]
    · rw [hcutg ξ hz, mul_one]
  have hg := (hb (h / r) (div_pos hh hr) ((div_le_one hr).mpr hhr) g).2
  rw [heq, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_spacetime_dilate _ (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable _ hr,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_schwartzDilate f _ hr] at hg
  simp only [ENNReal.toReal_ofReal hp.le, one_div_div] at hg
  let D : ℝ≥0∞ := ENNReal.ofReal ((r ^ (n + 1))⁻¹) ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hDt : D ≠ ⊤ := by dsimp [D]; finiteness
  apply (ENNReal.mul_le_mul_iff_right hD hDt).mp
  refine hg.trans_eq ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg hr.le _)),
    ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul hC.le,
    ← OAI.Analysis.Fourier.BochnerRiesz.spacetime_dilation_factor hr (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)]
  dsimp [D]
  ac_rfl

/-- Moving the logarithmic loss between scales costs at most a polynomial in
time, which can be absorbed by the Schwartz time cutoff. -/
theorem logarithmic_slab_weight_le {h r : ℝ} (hh : 0 < h) (h1 : h ≤ 1)
    (hr : 0 < r) :
    1 + Real.log (r / h) ≤ (1 + Real.log (1 / h)) * max 1 r := by
  have hL := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.logarithm_weight_one_le hh h1
  have heq : Real.log (r / h) = Real.log r + Real.log (1 / h) := by
    rw [Real.log_div hr.ne' hh.ne', Real.log_div one_ne_zero hh.ne', Real.log_one]
    ring
  rw [heq]
  by_cases hr1 : r ≤ 1
  · rw [max_eq_left hr1, mul_one]
    linarith [Real.log_nonpos hr.le hr1]
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    rw [max_eq_right hr1']
    have hlog := Real.log_le_sub_one_of_pos hr
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hr1')]

/-- Uniform positive-slab estimate with a logarithmic frequency loss and a
fixed polynomial time weight. -/
theorem logarithmic_all_positive_slabs (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h r : ℝ, 0 < h → h ≤ 1 → 0 < r →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.BochnerRiesz.timeSlabMeasure n r) ≤
      ENNReal.ofReal (r ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) * (max 1 r) ^ (2 * n + 5 : ℕ)) *
        (ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume) := by
  obtain ⟨A, hA, ha⟩ := logarithmic_annular_slab hlog hn hχ hc hzero
  have hp : 1 ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n :=
    le_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn).le
  obtain ⟨B, hB, hb⟩ := OAI.Analysis.Fourier.BochnerRiesz.shortTime_annular_slab hχ hc hzero hp
  refine ⟨A + B + 1, by linarith, ?_⟩
  intro h r hh hone hr f hcut
  have hL : 1 ≤ 1 + Real.log (1 / h) :=
    OAI.Analysis.Fourier.LocalSmoothing.Interpolation.logarithm_weight_one_le hh hone
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  apply le_trans (b := ENNReal.ofReal ((A + B + 1) * r ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) *
      (1 + Real.log (1 / h)) ^ (2 * n + 5) * (max 1 r) ^ (2 * n + 5)) *
      eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume)
  · by_cases hhr : h ≤ r
    · refine (ha h r hh hhr f hcut).trans (mul_le_mul' ?_ le_rfl)
      apply ENNReal.ofReal_le_ofReal
      have hLr : 0 ≤ 1 + Real.log (r / h) := by
        have : 1 ≤ r / h := (le_div_iff₀ hh).mpr (by simpa using hhr)
        linarith [Real.log_nonneg this]
      have hpow := pow_le_pow_left₀ hLr (logarithmic_slab_weight_le hh hone hr)
        (2 * n + 5)
      rw [mul_pow] at hpow
      calc
        _ ≤ A * r ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) *
            ((1 + Real.log (1 / h)) ^ (2 * n + 5) * (max 1 r) ^ (2 * n + 5)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = A * r ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) *
            (1 + Real.log (1 / h)) ^ (2 * n + 5) * (max 1 r) ^ (2 * n + 5) := by ring
        _ ≤ _ := by gcongr; linarith
    · refine (hb h r hr (le_of_not_ge hhr) f hcut).trans (mul_le_mul' ?_ le_rfl)
      apply ENNReal.ofReal_le_ofReal
      have hrone : r ≤ 1 := (le_of_not_ge hhr).trans hone
      rw [max_eq_left hrone, one_pow, mul_one]
      have hpow : 1 ≤ (1 + Real.log (1 / h)) ^ (2 * n + 5) := one_le_pow₀ hL
      calc
        _ ≤ (A + B + 1) * r ^ (1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) := by gcongr; linarith
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow
  · apply le_of_eq
    congr 2
    ring

end OAI.MeasureTheory.Kakeya
