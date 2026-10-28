import OAI.Analysis.Fourier.LocalSmoothing.DyadicReconstruction
import OAI.Analysis.Fourier.LocalSmoothing.DyadicWeights

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- Summable bounds for the actual annular half-wave pieces, together with
the low-frequency bound, give both membership and the full spacetime bound. -/
theorem smoothing_bound_of_dyadic_bounds {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Space n → ℂ} (hg : MemLp g p volume)
    {w : ℕ → ℝ} (hw₀ : ∀ j, 0 ≤ w j) (hw : Summable w)
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hlow : eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingLowCutoff 1 z.2 f z.1) p (observationMeasure n) ≤
      ENNReal.ofReal C₀ * eLpNorm g p volume)
    (hann : ∀ j, eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) z.2 f z.1)
        p (observationMeasure n) ≤
      ENNReal.ofReal (C₁ * w j) * eLpNorm g p volume) :
    MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ∧
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) p (observationMeasure n) ≤
      ENNReal.ofReal (C₀ + C₁ * ∑' j, w j) * eLpNorm g p volume := by
  have hsum : (∑' j, ENNReal.ofReal (C₁ * w j) * eLpNorm g p volume) =
      ENNReal.ofReal (C₁ * ∑' j, w j) * eLpNorm g p volume := by
    simp_rw [ENNReal.ofReal_mul hC₁]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg hw₀ hw, ← ENNReal.ofReal_mul hC₁]
  have hb : eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
      p (observationMeasure n) ≤
      ENNReal.ofReal (C₀ + C₁ * ∑' j, w j) * eLpNorm g p volume := by
    calc
      _ ≤ eLpNorm (fun z : Space n × ℝ ↦
          frequencyHalfWave smoothingLowCutoff 1 z.2 f z.1) p (observationMeasure n) +
          ∑' j, eLpNorm (fun z : Space n × ℝ ↦
            frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) z.2 f z.1)
            p (observationMeasure n) := eLpNorm_halfWave_le_dyadic f hp
      _ ≤ ENNReal.ofReal C₀ * eLpNorm g p volume +
          ∑' j, ENNReal.ofReal (C₁ * w j) * eLpNorm g p volume :=
        add_le_add hlow (ENNReal.tsum_le_tsum hann)
      _ = _ := by
        rw [hsum, ← add_mul, ← ENNReal.ofReal_add hC₀ (mul_nonneg hC₁ (tsum_nonneg hw₀))]
  refine ⟨?_, hb⟩
  exact lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top)

end OAI.Analysis.Fourier.LocalSmoothing
