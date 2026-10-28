import OAI.MeasureTheory.Kakeya.Log.Extension
import OAI.MeasureTheory.Kakeya.Log.VolumeExtension
import OAI.Analysis.Fourier.Restriction.CriticalInput

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem criticalExponent_conjugate {n : ℕ} (hn : 2 ≤ n) :
    OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n / (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n - 1) = OAI.Analysis.Fourier.Restriction.restrictionInputExponent n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have hsub : 2 * (n : ℝ) / ((n : ℝ) - 1) - 1 =
      ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
    field_simp
    ring
  unfold OAI.Analysis.Fourier.Restriction.restrictionInputExponent OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  rw [hsub]
  field_simp

theorem one_le_tube_observation_radius {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    1 ≤ 4 / δ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  nlinarith [sq_nonneg (1 - δ)]

/-- Passing to the parabolic observation radius preserves the logarithmic
degree. The multiplicative constant does not depend on the tube scale. -/
theorem tube_observation_log_bound (A : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (1 + Real.log (4 / δ ^ 2)) ^ A ≤
      (3 + Real.log 4) ^ A * (1 + Real.log (1 / δ)) ^ A := by
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg ((one_le_div hδ).mpr hδone)
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hid : Real.log (4 / δ ^ 2) = Real.log 4 + 2 * Real.log (1 / δ) := by
    rw [Real.log_div (by norm_num) (pow_ne_zero 2 hδ.ne'), Real.log_pow,
      Real.log_div one_ne_zero hδ.ne', Real.log_one]
    ring
  rw [hid, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg hfour hlog]

/-- Local restriction with a logarithmic loss dualizes to the exact local
extension estimate needed by the tube-packet argument. -/
theorem logarithmic_tube_extension_of_restriction {n A : ℕ} (hn : 2 ≤ n)
    (hrest : ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      (∀ y, R < ‖y‖ → f y = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        D * ENNReal.ofReal ((1 + Real.log R) ^ A) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
        MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ∧
        eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
          (volume.restrict (Metric.ball (0 : Space n) (4 / δ ^ 2))) ≤
          ENNReal.ofReal (C * (1 + Real.log (1 / δ)) ^ A) *
            eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  obtain ⟨D, hDt, hD⟩ := hrest
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  let C : ℝ := (D.toReal + 1) * (3 + Real.log 4) ^ A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro δ hδ hδone g hg
  have hDC : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hDt).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have hcoeff : D * ENNReal.ofReal ((1 + Real.log (4 / δ ^ 2)) ^ A) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / δ)) ^ A) := by
    calc
      _ ≤ ENNReal.ofReal (D.toReal + 1) *
          ENNReal.ofReal ((3 + Real.log 4) ^ A * (1 + Real.log (1 / δ)) ^ A) :=
        mul_le_mul' hDC (ENNReal.ofReal_le_ofReal (tube_observation_log_bound A hδ hδone))
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [C]
        ring
  apply sphericalExtension_bound_of_local_restriction
    (by linarith [criticalExponent_gt_two hn]) measurableSet_ball measure_ball_lt_top.ne
    ENNReal.ofReal_ne_top ?_ hg
  intro f hfm hfi hfp hfs
  rw [criticalExponent_conjugate hn] at hfp ⊢
  apply (hD (4 / δ ^ 2) (one_le_tube_observation_radius hδ hδone) f hfm hfi hfp ?_).trans
    (mul_le_mul' hcoeff le_rfl)
  intro y hy
  apply hfs y
  simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy.le

end OAI.MeasureTheory.Kakeya
