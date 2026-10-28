import OAI.Analysis.Fourier.SquareFunction.BoundaryConvergence
import OAI.Analysis.Fourier.SquareFunction.Scaling
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory FourierTransform Set Metric
open scoped ContDiff ENNReal

namespace OAI.Analysis.Fourier.SquareFunction

/-- The singular differentiated radial multiplier is integrable at unit
radius. A compact smooth Fourier cutoff extracts one good radius from
the square-function integrability theorem, and dilation removes that
radius. No pointwise domination across a moving singular sphere is used. -/
theorem integrable_radiusMultiplier_unit {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1/2 < α) :
    Integrable (fun ξ : Space n => radiusMultiplier α ‖ξ‖ 1) := by
  let b : ContDiffBump (0 : Space n) := ⟨2,3,by norm_num,by norm_num⟩
  let g : Space n → ℂ := fun ξ => (b ξ : ℂ)
  have hgd : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Space n) 3)
    intro ξ hξ
    have hnorm : 3 < ‖ξ‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hξ
    have hb : b ξ = 0 := b.zero_of_le_dist (by simpa using hnorm.le)
    simp only [g,hb,Complex.ofReal_zero]
  let G : SchwartzMap (Space n) ℂ := hgc.toSchwartzMap hgd
  let f : SchwartzMap (Space n) ℂ := 𝓕⁻ G
  have hF (ξ : Space n) : (𝓕 f) ξ = (b ξ : ℂ) := by
    dsimp only [f]
    rw [fourier_fourierInv_eq]
    rfl
  have hae := ae_integrable_radius_symbol_schwartz hα f
  have hsub : Ioo (1 : ℝ) 2 ⊆ Ioi 0 := fun r hr => by exact lt_trans zero_lt_one hr.1
  have hpos : volume (Ioo (1 : ℝ) 2) ≠ 0 := by simp
  obtain ⟨r,hr,hri⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae_restrict_of_subset hsub hae)
  have hrpos : 0 < r := lt_trans zero_lt_one hr.1
  have hc : Integrable (fun ξ : Space n => (radiusMultiplier α ‖ξ‖ r : ℂ)) := by
    apply hri.congr
    filter_upwards [] with ξ
    rw [hF]
    by_cases hξ : ‖ξ‖ < r
    · have hb : b ξ = 1 := b.one_of_mem_closedBall (by
        simpa only [mem_closedBall,dist_zero_right] using (hξ.trans hr.2).le)
      simp only [hb,Complex.ofReal_one,mul_one]
    · simp only [radiusMultiplier,ite_eq_right hξ,Complex.ofReal_zero,zero_mul]
  have hi : Integrable (fun ξ : Space n => radiusMultiplier α ‖ξ‖ r) := by
    simpa only [RCLike.re_to_complex,Complex.ofReal_re] using hc.re
  have hs := hi.comp_smul hrpos.ne'
  convert hs using 1
  funext ξ
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hrpos]
  simpa only [mul_one] using (radiusMultiplier_scale hrpos α ‖ξ‖ 1).symm

/-- Absolute integrability of the differentiated Bochner--Riesz symbol
at every positive radius, including the singular range `1/2 < α < 1`. -/
theorem integrable_radiusMultiplier {n : ℕ} [NeZero n] {α r : ℝ}
    (hα : 1/2 < α) (hr : 0 < r) :
    Integrable (fun ξ : Space n => radiusMultiplier α ‖ξ‖ r) := by
  have hi := (integrable_radiusMultiplier_unit (n:=n) hα).comp_smul (inv_ne_zero hr.ne')
  convert hi using 1
  funext ξ
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  simpa only [inv_mul_cancel₀ hr.ne'] using
    (radiusMultiplier_scale (inv_pos.mpr hr) α ‖ξ‖ r).symm

/-- The exact dilation law for the integrable radial derivative symbol. -/
theorem integral_radiusMultiplier_dilation {n : ℕ} (α : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ ξ : Space n, radiusMultiplier α ‖ξ‖ r) =
      r^n * ∫ ξ : Space n, radiusMultiplier α ‖ξ‖ 1 := by
  have he : (fun ξ : Space n => radiusMultiplier α ‖r⁻¹ • ξ‖ 1) =
      (fun ξ : Space n => radiusMultiplier α ‖ξ‖ r) := by
    funext ξ
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    simpa only [inv_mul_cancel₀ hr.ne'] using
      radiusMultiplier_scale (inv_pos.mpr hr) α ‖ξ‖ r
  have h := Measure.integral_comp_inv_smul volume
    (fun ξ : Space n => radiusMultiplier α ‖ξ‖ 1) r
  rw [he] at h
  simpa only [Space,finrank_euclideanSpace_fin,abs_of_nonneg (pow_nonneg hr.le n),
    smul_eq_mul] using h

end OAI.Analysis.Fourier.SquareFunction
