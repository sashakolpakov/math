import OAI.Analysis.Fourier.Restriction.Bumps
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem volume_finite_ball_union_le {n : ℕ} (E : Finset (Space n)) (r : ℝ) :
    volume (⋃ z ∈ E, ball z r) ≤ (E.card : ℝ≥0∞) * volume (ball (0 : Space n) r) := by
  have he (z : Space n) : volume (ball z r) = volume (ball (0 : Space n) r) := by
    have h := measure_preimage_add (volume : Measure (Space n)) z (ball z r)
    have hs : (fun x ↦ z + x) ⁻¹' ball z r = ball 0 r := by
      ext x
      simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
    rw [hs] at h
    exact h.symm
  calc
    _ ≤ ∑ z ∈ E, volume (ball z r) := measure_biUnion_finset_le E _
    _ = _ := by simp only [he, Finset.sum_const, nsmul_eq_mul]

theorem eLpNorm_separatedBumpSum_le {n : ℕ} {p : ℝ} (hp : 0 < p)
    (E : Finset (Space n)) (a : Space n → ℂ)
    (hsep : ∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w)
    (ha : ∀ z ∈ E, ‖a z‖ ≤ 1) :
    eLpNorm (separatedBumpSum E a) (ENNReal.ofReal p) volume ≤
      ((E.card : ℝ≥0∞) * volume (ball (0 : Space n) (1 / 4))) ^ (1 / p) := by
  have H := eLpNorm_le_bound_mul_measure volume
    (measurable_separatedBumpSum E a).aestronglyMeasurable
    (E.measurableSet_biUnion (fun _ _ ↦ measurableSet_ball)) (by norm_num : (0 : ℝ) ≤ 1)
    (separatedBumpSum_norm_le_one E a hsep ha)
    (E := ⋃ z ∈ E, ball z (1 / 4))
    (by
      intro x hx
      apply separatedBumpSum_eq_zero
      simpa only [mem_iUnion, not_exists, not_and] using hx) hp
  simp only [ENNReal.ofReal_one, one_mul] at H
  exact H.trans (ENNReal.rpow_le_rpow (volume_finite_ball_union_le E _) (by positivity))

theorem eLpNorm_finitePhaseSum_le_bumps {n : ℕ} (E : Finset (Space n))
    (a : Space n → ℂ) (p : ℝ≥0∞) :
    ENNReal.ofReal (volume.real (ball (0 : Space n) (1 / 4)) / 2) *
        eLpNorm (finitePhaseSum E a) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (separatedBumpSum E a)) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  let c := volume.real (ball (0 : Space n) (1 / 4)) / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have H : eLpNorm ((c : ℂ) • finitePhaseSum E a) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (separatedBumpSum E a)) p (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply eLpNorm_mono_ae ((continuous_finitePhaseSum E a).const_smul (c : ℂ)).aestronglyMeasurable
    filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ξ hξ
    have Hlow := small_ball_fourier_lower (n := n) (r := 1 / 4) le_rfl (le_of_eq hξ)
    rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
      angularFourier_separatedBumpSum, norm_mul]
    exact mul_le_mul_of_nonneg_right Hlow (norm_nonneg _)
  simpa only [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc] using H

end OAI.Analysis.Fourier.Restriction
