import OAI.MeasureTheory.Kakeya.Log.Smoothing
import OAI.Analysis.Fourier.BochnerRiesz.ProjectedShell
import OAI.Analysis.Fourier.BochnerRiesz.Shell.Operator
import OAI.Analysis.Fourier.BochnerRiesz.PacketNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem logarithmic_projected_shell (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ ψ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hzero : (0 : Space n) ∉ tsupport ψ)
    (hcover : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1) (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ s : ℝ,
      (∀ ξ : Space n, φ (s - ‖ξ‖) ≠ 0 → χ (h • ((2 * Real.pi) • ξ)) = 1) →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨A, hA, ha⟩ := OAI.Analysis.Fourier.BochnerRiesz.annularProject_uniform_bound hχ hcχ
  obtain ⟨B, hB, hb⟩ := logarithmic_thinShellCycles hlog hn hψ hcψ hzero φ
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro h hh hh1 s hcut f
  have H := (hb h hh hh1 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f)
    (OAI.Analysis.Fourier.BochnerRiesz.annularProject_support_cutoff hχ hcχ hh f hcover) s).2
  have he : (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 (OAI.Analysis.Fourier.BochnerRiesz.annularProject χ h f) x s) =
      (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) := by
    funext x
    exact OAI.Analysis.Fourier.BochnerRiesz.thinShellCycles_annularProject hχ hcχ hh φ 1 s f (by simpa only [div_one] using hcut) x
  rw [he] at H
  have hp1 : 1 ≤ ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (le_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn).le)
  have hL := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.logarithm_weight_one_le hh hh1
  refine H.trans ((mul_le_mul' le_rfl (ha h hh f _ hp1 ENNReal.ofReal_ne_top)).trans_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

theorem eLpNorm_dilatedShellCycles_bound {n : ℕ} (φ : SchwartzMap ℝ ℂ) (Λ : ℝ)
    {p B : ℝ≥0∞}
    (hlocal : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles φ Λ 1 g) p volume ≤ B * eLpNorm g p volume)
    {r : ℝ} (hr : 0 < r) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles φ Λ r f) p volume ≤ B * eLpNorm f p volume := by
  have H := hlocal (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate r hr.ne' f)
  have he : OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles φ Λ 1 (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate r hr.ne' f) =
      fun x ↦ OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles φ Λ r f (r • x) := by
    funext x
    simpa only [one_mul] using OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles_schwartzDilate φ Λ 1 hr f x
  rw [he, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_dilate_enormed _ p hr, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_schwartzDilate f p hr] at H
  let D : ℝ≥0∞ := ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p.toReal)
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hDtop : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hD0 hDtop).mp
  simpa only [D, mul_left_comm, mul_assoc] using H

/-- A fixed compact profile gives a uniform logarithmic thin-shell estimate
at every dilation, including shells of width `T⁻¹` around the unit sphere. -/
theorem logarithmic_dilated_shell (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) (φ : SchwartzMap ℝ ℂ)
    (hφ : ∀ t, φ t ≠ 0 → |t| ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℝ, 0 < ρ →
      ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles φ T ρ f) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨χ, hχ, hcχ, _, honeχ, hbandχ⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
    (a := Real.pi / 4) (b := Real.pi / 2) (c := 4 * Real.pi) (d := 8 * Real.pi)
    (by positivity) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  obtain ⟨ψ, hψ, hcψ, hzeroψ, honeψ, _⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
    (a := Real.pi / 8) (b := Real.pi / 4) (c := 8 * Real.pi) (d := 16 * Real.pi)
    (by positivity) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hcover : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1 := by
    intro ξ hξ
    exact honeψ ξ (hbandχ ξ hξ).1.le (hbandχ ξ hξ).2.le
  obtain ⟨C, hC, hb⟩ := logarithmic_projected_shell hlog hn hχ hcχ hψ hcψ hzeroψ hcover φ
  refine ⟨C, hC, ?_⟩
  intro T hT ρ hρ f
  have hT0 : 0 < T := by linarith
  have hh : T⁻¹ ≤ 1 := (inv_le_one₀ hT0).mpr hT
  have hcut : ∀ ξ : Space n,
      φ (T - ‖ξ‖) ≠ 0 → χ (T⁻¹ • ((2 * Real.pi) • ξ)) = 1 := by
    intro ξ hξ
    have hphase := abs_le.mp (hφ (T - ‖ξ‖) hξ)
    have hlo : T / 4 ≤ ‖ξ‖ := by linarith
    have hhi : ‖ξ‖ ≤ 2 * T := by linarith
    have he : ‖T⁻¹ • ((2 * Real.pi) • ξ)‖ = (2 * Real.pi * ‖ξ‖) / T := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hT0), abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      ring
    apply honeχ
    · rw [he]
      apply (le_div_iff₀ hT0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 * Real.pi)]
    · rw [he]
      apply (div_le_iff₀ hT0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 2 * Real.pi)]
  apply eLpNorm_dilatedShellCycles_bound φ T _ hρ f
  intro g
  have he : OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles φ T 1 g = fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 g x T := by
    funext x
    simpa only [div_one] using OAI.Analysis.Fourier.BochnerRiesz.dilatedShellCycles_eq_thinShellCycles φ T one_ne_zero g x
  rw [he]
  simpa only [one_div, inv_inv] using hb T⁻¹ (inv_pos.mpr hT0) hh T hcut g

/-- Fixed smooth spatial-frequency weights do not worsen the logarithmic
loss for the normalized unit-frequency shell. -/
theorem logarithmic_weighted_unit_shell (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {a : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (φ : SchwartzMap ℝ ℂ) (hφ : ∀ t, φ t ≠ 0 → |t| ≤ 1 / 4)
    (heven : ∀ t, φ (-t) = φ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ a ξ * φ (T * (‖ξ‖ - 1))) 1 0 f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log T) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨B, hB, hb⟩ := logarithmic_dilated_shell hlog hn φ hφ
  obtain ⟨A, hA, hkernel⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_angularInverse_kernel_bound ha hc
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro T hT f
  have hT0 : 0 < T := by linarith
  have hp : 1 ≤ ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (le_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn).le)
  have H := OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_fourierInv_dilated_smooth_factor_le ha hc zero_lt_one
    (OAI.Analysis.Fourier.BochnerRiesz.integrable_dilatedShellSymbol φ T (2 * Real.pi * T) f) hp ENNReal.ofReal_ne_top
  have he : (𝓕⁻ (fun ξ : Space n ↦ a ((1 : ℝ) • ((2 * Real.pi) • ξ)) *
      (φ (T - (2 * Real.pi * T) * ‖ξ‖) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ))) =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ a ξ * φ (T * (‖ξ‖ - 1))) 1 0 f := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_fourierInv]
    congr 1
    funext ξ
    simp only [one_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), SchwartzMap.fourier_coe]
    have ht : T - (2 * Real.pi * T) * ‖ξ‖ = -(T * (2 * Real.pi * ‖ξ‖ - 1)) := by ring
    rw [ht, heven]
    ring
  rw [he] at H
  refine H.trans ((mul_le_mul' hkernel (hb T hT (2 * Real.pi * T) (by positivity) f)).trans_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le]
  congr 2
  ring

end OAI.MeasureTheory.Kakeya
