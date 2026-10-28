import OAI.Analysis.Fourier.BochnerRiesz.TimeReversal
import Mathlib.Analysis.MeanInequalitiesPow

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem eLpNorm_add_measure_le_real {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f (μ + ν))
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm f (ENNReal.ofReal p) (μ + ν) ≤
      eLpNorm f (ENNReal.ofReal p) μ + eLpNorm f (ENNReal.ofReal p) ν := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hm := hf.mono_measure (Measure.le_add_right (le_refl μ))
  have hn := hf.mono_measure (Measure.le_add_left (le_refl ν))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hn,
    ENNReal.toReal_ofReal hp0.le, lintegral_add_measure]
  exact ENNReal.rpow_add_le_add_rpow _ _ (by positivity) ((div_le_one hp0).mpr hp)

theorem positiveTimeMeasure_add_negativeTimeMeasure (n : ℕ) :
    positiveTimeMeasure n + negativeTimeMeasure n =
      (volume : Measure (Space n)).prod (volume : Measure ℝ) := by
  unfold positiveTimeMeasure negativeTimeMeasure
  rw [← Measure.prod_add, restrict_Iio_eq_restrict_Iic]
  simpa only [Set.compl_Ioi] using congrArg ((volume : Measure (Space n)).prod)
    (Measure.restrict_add_restrict_compl (μ := (volume : Measure ℝ)) measurableSet_Ioi)

/-- Positive-loss local smoothing gives the weighted all-time annular estimate.
The time decay exponent only needs to exceed the Sobolev loss plus `1/p`. -/
theorem localSmoothing_weighted_all_time (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p ε M : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hM : 1 / p + (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      MemLp (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal p) (volume.prod volume) ∧
      eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal p) (volume.prod volume) ≤
      ENNReal.ofReal (C * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA, ha⟩ := localSmoothing_positive_weighted hls hn hχ hc hzero hp hε hM
  obtain ⟨B, hB, hb⟩ := localSmoothing_negative_weighted hls hn hχ hc hzero hp hε hM
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro h hh hone f hcut
  have hF := continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)
  have H : eLpNorm (weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
      (ENNReal.ofReal p) (volume.prod volume) ≤
      ENNReal.ofReal ((A + B) * h ^ (-(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε))) *
        eLpNorm f (ENNReal.ofReal p) volume := by
    rw [← positiveTimeMeasure_add_negativeTimeMeasure n]
    refine (eLpNorm_add_measure_le_real hF.aestronglyMeasurable (by linarith : 1 ≤ p)).trans ?_
    refine (add_le_add (ha h hh hone f hcut) (hb h hh hone f hcut)).trans_eq ?_
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hA.le (Real.rpow_nonneg hh.le _))
      (mul_nonneg hB.le (Real.rpow_nonneg hh.le _)), ← add_mul]
  refine ⟨?_, H⟩
  exact H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top)

end OAI.Analysis.Fourier.BochnerRiesz
