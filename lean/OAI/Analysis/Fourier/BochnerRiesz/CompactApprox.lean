import OAI.Analysis.Fourier.SquareFunction.ConvolutionDensity
import OAI.Analysis.Fourier.BochnerRiesz.Cutoff

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem exists_schwartz_compact_approx {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {f : Space n → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hfp : MemLp f p volume)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ x, R < ‖x‖ → f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SchwartzMap (Space n) ℂ,
      (∀ x, R + 2 ≤ ‖x‖ → g x = 0) ∧
      eLpNorm (f - (g : Space n → ℂ)) p volume ≤ ENNReal.ofReal ε := by
  obtain ⟨u, hu⟩ := OAI.Analysis.Fourier.SquareFunction.exists_schwartz_eLpNorm_sub_le hp hpt hfp hε
  let b : ContDiffBump (0 : Space n) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let g : Space n → ℂ := fun x => (b x : ℂ) * u x
  have hgd : ContDiff ℝ ∞ g := (Complex.ofRealCLM.contDiff.comp b.contDiff).mul (u.smooth ⊤)
  have hgzero (x : Space n) (hx : R + 2 ≤ ‖x‖) : g x = 0 := by
    have hb : b x = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    simp only [g, hb, Complex.ofReal_zero, zero_mul]
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Space n) (R + 2))
    intro x hx
    apply hgzero x
    have h := not_le.mp (by simpa only [mem_closedBall, dist_zero_right] using hx)
    exact h.le
  refine ⟨hgc.toSchwartzMap hgd, hgzero, ?_⟩
  apply le_trans _ hu
  apply eLpNorm_mono (hfm.sub hgd.continuous.aestronglyMeasurable)
  intro x
  have he : f x - g x = (b x : ℂ) * (f x - u x) := by
    by_cases hx : ‖x‖ ≤ R
    · have hb : b x = 1 := b.one_of_mem_closedBall (by
        simp only [mem_closedBall, dist_zero_right]
        change ‖x‖ ≤ R + 1
        linarith)
      simp [g, hb]
    · rw [hs x (lt_of_not_ge hx)]
      simp [g]
  change ‖f x - g x‖ ≤ ‖f x - u x‖
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) b.le_one

theorem eLpNorm_one_le_compact {n : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : Space n → ℂ} (hf : AEStronglyMeasurable f volume)
    {R : ℝ} (hs : Function.support f ⊆ closedBall 0 R) :
    eLpNorm f 1 volume ≤ eLpNorm f p volume *
      volume (closedBall (0 : Space n) R) ^ (1 - 1 / p.toReal) := by
  have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (closedBall 0 R)) hp hf.restrict
  simpa only [eLpNorm_restrict_eq_of_support_subset hf hs, Measure.restrict_apply_univ,
    ENNReal.toReal_one, div_one] using H

/-- Approximation in both norms uses one fixed compact spatial cutoff. -/
theorem exists_schwartz_compact_approx_two_norms {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {f : Space n → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hfp : MemLp f p volume)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ x, R < ‖x‖ → f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SchwartzMap (Space n) ℂ,
      eLpNorm (f - (g : Space n → ℂ)) p volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - (g : Space n → ℂ)) 1 volume ≤ ENNReal.ofReal ε := by
  let D : ℝ≥0∞ := volume (closedBall (0 : Space n) (R + 2)) ^ (1 - 1 / p.toReal)
  have hpR : (1 : ℝ) ≤ p.toReal := by
    simpa using (ENNReal.toReal_mono hpt hp)
  have he : 0 ≤ 1 - 1 / p.toReal := by
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpR
    norm_num only [div_one] at H
    linarith
  have hD : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg he measure_closedBall_lt_top.ne
  obtain ⟨η, hη, hηbound⟩ := OAI.Analysis.Fourier.SquareFunction.exists_pos_mul_ofReal_le
    (C := 1 + D) (ENNReal.add_ne_top.mpr ⟨by simp, hD⟩)
    (ε := ⟨ε, hε.le⟩) hε
  have hηbound' : (1 + D) * ENNReal.ofReal η ≤ ENNReal.ofReal ε := by
    convert hηbound using 1
    exact ENNReal.ofReal_eq_coe_nnreal hε.le
  obtain ⟨g, hgzero, hgp⟩ := exists_schwartz_compact_approx hp hpt hfm hfp hR hs hη
  have hs' : Function.support (f - (g : Space n → ℂ)) ⊆ closedBall 0 (R + 2) := by
    intro x hx
    by_contra hn
    have hxR : R + 2 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hn
    apply hx
    simp only [Pi.sub_apply, hs x (by linarith), hgzero x hxR.le, sub_zero]
  refine ⟨g, hgp.trans ?_, ?_⟩
  · calc
      ENNReal.ofReal η = 1 * ENNReal.ofReal η := (one_mul _).symm
      _ ≤ (1 + D) * ENNReal.ofReal η := mul_le_mul' le_self_add le_rfl
      _ ≤ _ := hηbound'
  · apply (eLpNorm_one_le_compact hp (hfm.sub g.continuous.aestronglyMeasurable) hs').trans
    change eLpNorm (f - (g : Space n → ℂ)) p volume * D ≤ _
    calc
      _ ≤ ENNReal.ofReal η * D := mul_le_mul' hgp le_rfl
      _ ≤ (1 + D) * ENNReal.ofReal η := by
        rw [mul_comm]
        exact mul_le_mul' le_add_self le_rfl
      _ ≤ _ := hηbound'

end OAI.Analysis.Fourier.BochnerRiesz
