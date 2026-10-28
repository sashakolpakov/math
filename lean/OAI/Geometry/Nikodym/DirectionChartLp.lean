import OAI.Geometry.Nikodym.DirectionChartIntegral

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def directionChartFactor (d : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (projectiveDistortion 1 (2*R)+1)^(d+1) *
    ENNReal.ofReal ((2*(R+1))*(2*(R+1))^d)

theorem map_chartDirection_le {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Measure.map (chartDirection d) (volume.restrict (closedBall 0 R)) ≤
      directionChartFactor d R • OAI.Analysis.Fourier.Restriction.sphereMeasure (d+1) := by
  apply Measure.le_iff.mpr
  intro A hA
  have h := lintegral_chartDirection_le hR (measurable_const.indicator hA :
    Measurable (A.indicator (fun _ : Space (d+1) => (1:ℝ≥0∞))))
  rw [← lintegral_map (measurable_const.indicator hA) (measurable_chartDirection d)] at h
  simp only [lintegral_indicator hA,lintegral_const,Measure.restrict_apply_univ,one_mul] at h
  simpa only [directionChartFactor,Measure.smul_apply,smul_eq_mul,mul_assoc] using h

theorem eLpNorm_chartDirection_le {d : ℕ} {R : ℝ} (hR : 0 < R)
    {H : Space (d+1) → ℝ≥0∞} (hH : Measurable H) (p : ℝ≥0∞) :
    eLpNorm (H ∘ chartDirection d) p (volume.restrict (closedBall 0 R)) ≤
      (directionChartFactor d R)^(1/p).toReal * eLpNorm H p (OAI.Analysis.Fourier.Restriction.sphereMeasure (d+1)) := by
  rw [← eLpNorm_map_measure hH.aestronglyMeasurable (measurable_chartDirection d).aemeasurable]
  exact eLpNorm_le_of_measure_le_smul (map_chartDirection_le hR)

end OAI.Geometry.Nikodym
