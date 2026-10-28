import OAI.Analysis.Fourier.Restriction.SmoothInverse
import OAI.Analysis.Fourier.Restriction.WeightedPhase
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sparse_cutoff_exists (n : ℕ) :
    ∃ u : SchwartzMap (Space n) ℂ, ∃ c : ℝ, 0 < c ∧
      (∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖) ∧
      (∀ ξ, star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) = OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) ∧
      (∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1) ∧
      (∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0) := by
  let b : ContDiffBump (0 : Space n) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  let χ : Space n → ℂ := fun ξ ↦ (b ξ : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχs : Function.support χ = Function.support b := by
    ext ξ
    simp only [Function.mem_support, χ, ne_eq, Complex.ofReal_eq_zero]
  have hχc : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hχs]
    exact b.hasCompactSupport
  have hbi : Integrable b := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hbp : 0 < ∫ ξ, b ξ := by
    apply (integral_pos_iff_support_of_nonneg b.nonneg' hbi).mpr
    rw [b.support_eq]
    exact measure_ball_pos volume _ (by norm_num [b])
  obtain ⟨u, hu, hFu⟩ := exists_schwartz_angularInverse_pair hχ hχc
  let N : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨u, N * (∫ ξ, b ξ) / 2, by positivity, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hphase : ∀ ξ, b ξ ≠ 0 → |inner ℝ x ξ| ≤ 1 / 4 := by
      intro ξ hξ
      have hb : ‖ξ‖ < 1 / 8 := by
        have : ξ ∈ Function.support b := hξ
        rw [b.support_eq] at this
        simpa only [b, mem_ball, dist_zero_right] using this
      calc
        _ ≤ ‖x‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ ≤ 1 / 4 := by linarith
    have H := weighted_small_phase_lower hbi b.nonneg'
      (show Measurable (fun ξ : Space n ↦ inner ℝ x ξ) by fun_prop) hphase
    have hxU := congrFun hu x
    rw [hxU, OAI.Analysis.Fourier.LocalSmoothing.angularInverse, norm_smul, Real.norm_eq_abs, abs_of_pos hN]
    change N * (∫ ξ, b ξ) / 2 ≤ N * ‖∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * (b ξ : ℂ)‖
    nlinarith
  · intro ξ
    rw [hFu]
    simp only [χ, Complex.star_def, Complex.conj_ofReal]
  · intro ξ
    rw [hFu]
    simpa only [χ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg] using b.le_one (x := ξ)
  · intro ξ hξ
    rw [hFu]
    have hb : b ξ = 0 := b.zero_of_le_dist (by simpa only [b, dist_zero_right] using hξ)
    simp only [χ, hb, Complex.ofReal_zero]

end OAI.Analysis.Fourier.Restriction
