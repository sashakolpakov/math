import OAI.MeasureTheory.Kakeya.Log.SmoothingShell
import OAI.MeasureTheory.Kakeya.Log.Kernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem contDiff_cutoff_norm_rpow {n : ℕ} (β : ℝ) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hzero : (0 : Space n) ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun ξ : Space n ↦ χ ξ * (‖ξ‖ ^ β : ℝ)) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hs : ξ ∈ tsupport χ
  · have hξ : ξ ≠ 0 := by intro h; subst ξ; exact hzero hs
    exact hχ.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      ((contDiffAt_norm ℝ hξ).rpow_const_of_ne (norm_ne_zero_iff.mpr hξ)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- Multiplication by a fixed radial power on the thin annulus only changes
the constant, not the logarithmic loss. -/
theorem logarithmic_power_weighted_unit_shell (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ t, φ t ≠ 0 → |t| ≤ 1 / 4)
    (heven : ∀ t, φ (-t) = φ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ (‖ξ‖ ^ β : ℝ) * φ (T * (‖ξ‖ - 1))) 1 0 f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨χ, hχ, hcχ, hzero, hone, _⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
    (a := 1 / 2) (b := 3 / 4) (c := 5 / 4) (d := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let a : Space n → ℂ := fun ξ ↦ χ ξ * (‖ξ‖ ^ β : ℝ)
  have ha : ContDiff ℝ ∞ a := contDiff_cutoff_norm_rpow β hχ hzero
  have hc : HasCompactSupport a := hcχ.mul_right
  obtain ⟨C, hC, hb⟩ := logarithmic_weighted_unit_shell hlog hn ha hc φ hφ heven
  refine ⟨C, hC, ?_⟩
  intro T hT f
  have he : (fun ξ : Space n ↦ a ξ * φ (T * (‖ξ‖ - 1))) =
      (fun ξ : Space n ↦ (‖ξ‖ ^ β : ℝ) * φ (T * (‖ξ‖ - 1))) := by
    funext ξ
    by_cases hz : φ (T * (‖ξ‖ - 1)) = 0
    · simp only [hz, mul_zero]
    · have hphase := abs_le.mp (hφ _ hz)
      have hlo : 3 / 4 ≤ ‖ξ‖ := by
        by_contra! H
        nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ 1 - ‖ξ‖ by linarith)]
      have hhi : ‖ξ‖ ≤ 5 / 4 := by
        by_contra! H
        nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ ‖ξ‖ - 1 by linarith)]
      simp only [a, hone ξ hlo hhi, one_mul]
  simpa only [he] using hb T hT f

/-- The weighted narrow kernel used for the quantitative restriction
argument has a critical multiplier norm bounded by a fixed logarithm. -/
theorem logarithmic_narrow_multiplier (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {φ : ℝ → ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4))
    (heven : ∀ t, φ (-t) = φ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (narrowSymbol n φ T) 1 0 f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  have hc : HasCompactSupport φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) hφ
  let Φ : SchwartzMap ℝ ℂ := (hc.toSchwartzMap hφc).postcompCLM Complex.ofRealCLM
  have hΦ : ∀ t, Φ t ≠ 0 → |t| ≤ 1 / 4 := by
    intro t ht
    have hne : φ t ≠ 0 := by
      intro hz
      apply ht
      change (φ t : ℂ) = 0
      simp [hz]
    exact abs_le.mpr (hφ (subset_tsupport φ hne))
  have heΦ : ∀ t, Φ (-t) = Φ t := by
    intro t
    change (φ (-t) : ℂ) = (φ t : ℂ)
    rw [heven]
  obtain ⟨C, hC, hb⟩ := logarithmic_power_weighted_unit_shell hlog hn
    (-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n) Φ hΦ heΦ
  refine ⟨C, hC, ?_⟩
  intro T hT f
  have he : (fun ξ : Space n ↦ (‖ξ‖ ^ (-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n) : ℝ) *
      Φ (T * (‖ξ‖ - 1))) = narrowSymbol n φ T := by
    funext ξ
    change (‖ξ‖ ^ (-OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n) : ℝ) * (φ (T * (‖ξ‖ - 1)) : ℂ) = _
    simp only [narrowSymbol, narrowProfile, Complex.ofReal_mul]
  simpa only [he] using hb T hT f

end OAI.MeasureTheory.Kakeya
