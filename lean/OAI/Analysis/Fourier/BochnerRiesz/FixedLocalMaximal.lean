import OAI.Analysis.Fourier.BochnerRiesz.LocalMaximal
import OAI.Analysis.Fourier.BochnerRiesz.Cutoff

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem localSmoothing_dyadicShellMax_of_support (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) (φ : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : ∀ t, φ t ≠ 0 → |t| ≤ R) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → 2 * R ≤ Λ → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * Λ ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨χ, hχ, hcχ, hzeroχ, honeχ, hbandχ⟩ := exists_annular_cutoff (n := n)
    (a := Real.pi / 4) (b := Real.pi / 2) (c := 4 * Real.pi) (d := 8 * Real.pi)
    (by positivity) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  obtain ⟨ψ, hψ, hcψ, hzeroψ, honeψ, hbandψ⟩ := exists_annular_cutoff (n := n)
    (a := Real.pi / 8) (b := Real.pi / 4) (c := 8 * Real.pi) (d := 16 * Real.pi)
    (by positivity) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hcover : ∀ ξ, χ ξ ≠ 0 → ψ ξ = 1 := by
    intro ξ hξ
    exact honeψ ξ (hbandχ ξ hξ).1.le (hbandχ ξ hξ).2.le
  obtain ⟨C, hC, hmax⟩ := localSmoothing_dyadicShellMax hls hn hχ hcχ hψ hcψ hzeroψ hcover φ hp hε
  refine ⟨C, hC, ?_⟩
  intro Λ hΛ hΛR f
  have hΛ0 : 0 < Λ := by linarith
  have hh : Λ⁻¹ ≤ 1 := (inv_le_one₀ hΛ0).mpr hΛ
  have hcut : ∀ ρ ∈ Icc (1 : ℝ) 2, ∀ ξ : Space n,
      φ (Λ - ρ * ‖ξ‖) ≠ 0 → χ (Λ⁻¹ • ((2 * Real.pi) • ξ)) = 1 := by
    intro ρ hρ ξ hξ
    have hphase := abs_le.mp (hR (Λ - ρ * ‖ξ‖) hξ)
    have hlo : Λ / 4 ≤ ‖ξ‖ := by nlinarith [hρ.2, norm_nonneg ξ]
    have hhi : ‖ξ‖ ≤ 2 * Λ := by nlinarith [hρ.1, norm_nonneg ξ]
    have he : ‖Λ⁻¹ • ((2 * Real.pi) • ξ)‖ = (2 * Real.pi * ‖ξ‖) / Λ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hΛ0), abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      ring
    apply honeχ
    · rw [he]
      apply (le_div_iff₀ hΛ0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 * Real.pi)]
    · rw [he]
      apply (div_le_iff₀ hΛ0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 2 * Real.pi)]
  have H := hmax Λ⁻¹ (inv_pos.mpr hΛ0) hh Λ hcut f
  simpa only [Real.inv_rpow hΛ0.le, Real.rpow_neg hΛ0.le, inv_inv] using H

/-- Local smoothing implies the local-in-dilation maximal thin-annulus
estimate for every smooth compactly supported profile. -/
theorem localSmoothing_dyadicShellMax_compact (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) (φ : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (φ : ℝ → ℂ))
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ L : ℝ, 1 ≤ L ∧ ∀ Λ : ℝ, L ≤ Λ → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (dyadicShellMax φ Λ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * Λ ^ (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε)) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ)
  have hr : ∀ t, φ t ≠ 0 → |t| ≤ R := by
    intro t ht
    have h := hR (subset_closure ht)
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using h
  obtain ⟨C, hC, hmax⟩ := localSmoothing_dyadicShellMax_of_support hls hn φ R hr hp hε
  refine ⟨C, hC, max 1 (2 * R), le_max_left _ _, ?_⟩
  intro Λ hΛ f
  exact hmax Λ ((le_max_left _ _).trans hΛ) ((le_max_right _ _).trans hΛ) f

end OAI.Analysis.Fourier.BochnerRiesz
