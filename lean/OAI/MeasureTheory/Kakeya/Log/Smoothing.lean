import OAI.MeasureTheory.Kakeya.Log.SmoothingSlabs
import OAI.Analysis.Fourier.BochnerRiesz.AllTime
import OAI.Analysis.Fourier.BochnerRiesz.Shell.Bound

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff Topology ComplexConjugate

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem logarithmic_positive_weighted (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {M : ℝ} (hM : 1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n + (2 * n + 5 : ℕ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.BochnerRiesz.positiveTimeMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨A, hA, ha⟩ := logarithmic_all_positive_slabs hlog hn hχ hc hzero
  have hp : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n :=
    lt_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn)
  obtain ⟨D, hD, hd⟩ := OAI.Analysis.Fourier.BochnerRiesz.positive_weighted_bound_from_slabs hp
    (Nat.cast_nonneg (2 * n + 5)) hM
  refine ⟨D * A, mul_pos hD hA, ?_⟩
  intro h hh hone f hcut
  have H := hd n _ (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)
    (ENNReal.ofReal (A * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
      eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume)
    (by simpa only [Real.rpow_natCast] using fun r hr ↦ ha h r hh hone hr f hcut)
  convert H using 1
  rw [ENNReal.ofReal_mul (mul_nonneg hD.le hA.le), ENNReal.ofReal_mul hD.le,
    ENNReal.ofReal_mul hA.le]
  ac_rfl

theorem logarithmic_negative_weighted (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {M : ℝ} (hM : 1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n + (2 * n + 5 : ℕ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.BochnerRiesz.negativeTimeMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  have hχ' : ContDiff ℝ ∞ (fun ξ : Space n ↦ χ (-ξ)) := hχ.comp contDiff_neg
  have hc' : HasCompactSupport (fun ξ : Space n ↦ χ (-ξ)) := by
    simpa only [neg_one_smul] using hc.comp_smul (show (-1 : ℝ) ≠ 0 by norm_num)
  have hz' : (0 : Space n) ∉ tsupport (fun ξ : Space n ↦ χ (-ξ)) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    exact (notMem_tsupport_iff_eventuallyEq.mp hzero).comp_tendsto
      (show Filter.Tendsto (fun ξ : Space n ↦ -ξ) (𝓝 0) (𝓝 0) by
        simpa only [neg_zero] using continuous_neg.tendsto (0 : Space n))
  obtain ⟨C, hC, hb⟩ := logarithmic_positive_weighted hlog hn hχ' hc' hz' hM
  refine ⟨C, hC, ?_⟩
  intro h hh hone f hcut
  have hcut' : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) ξ ≠ 0 → χ (-(h • ξ)) = 1 := by
    intro ξ hξ
    have hfξ : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (-ξ) ≠ 0 := by
      intro hz
      apply hξ
      change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ conj (f x)) ξ = 0
      rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_conj, hz, map_zero]
    simpa only [smul_neg] using hcut (-ξ) hfξ
  have H := hb h hh hone (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) hcut'
  rwa [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_weighted_schwartzConj, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_schwartzConj] at H

/-- The critical all-time estimate loses only a fixed power of a logarithm in
frequency; its time weight is independent of the frequency scale. -/
theorem logarithmic_weighted_all_time (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {M : ℝ} (hM : 1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n + (2 * n + 5 : ℕ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (volume.prod volume) ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (volume.prod volume) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨A, hA, ha⟩ := logarithmic_positive_weighted hlog hn hχ hc hzero hM
  obtain ⟨B, hB, hb⟩ := logarithmic_negative_weighted hlog hn hχ hc hzero hM
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro h hh hone f hcut
  have hL := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.logarithm_weight_one_le hh hone
  have hF := OAI.Analysis.Fourier.BochnerRiesz.continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)
  have hp : 1 ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n :=
    le_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn).le
  have H : eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
      (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (volume.prod volume) ≤
      ENNReal.ofReal ((A + B) * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
    rw [← OAI.Analysis.Fourier.BochnerRiesz.positiveTimeMeasure_add_negativeTimeMeasure n]
    refine (OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_add_measure_le_real hF.aestronglyMeasurable hp).trans ?_
    refine (add_le_add (ha h hh hone f hcut) (hb h hh hone f hcut)).trans_eq ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul]
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (f.memLp _ volume).eLpNorm_lt_top), H⟩

/-- At the critical exponent the thin-shell multiplier has a polylogarithmic,
not a positive-power, frequency loss. -/
theorem logarithmic_thinShellCycles (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) → ∀ s : ℝ,
      MemLp (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ∧
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume ≤
        ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  let p := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n
  let M : ℝ := 1 / p + (2 * n + 5 : ℕ) + 1
  have hM : 1 / OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n + (2 * n + 5 : ℕ) < M := by dsimp [M, p]; linarith
  obtain ⟨B, hB, hb⟩ := logarithmic_weighted_all_time hlog hn hχ hc hzero hM
  obtain ⟨A, hA, ha⟩ := OAI.Analysis.Fourier.BochnerRiesz.thinShellCycles_weighted_domination φ M
  have hp : 1 ≤ p :=
    le_trans (by norm_num) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.criticalExponent_gt_two hn).le
  let D : ℝ≥0∞ := ENNReal.ofReal A * (∫⁻ t : ℝ, OAI.Analysis.Fourier.BochnerRiesz.timeDensity t) ^ ((p - 1) / p)
  have hpexp : 0 ≤ (p - 1) / p := div_nonneg (by linarith) (by linarith)
  have hD : D ≠ ⊤ := by
    apply ne_of_lt
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.rpow_lt_top_of_nonneg hpexp OAI.Analysis.Fourier.BochnerRiesz.lintegral_timeDensity_lt_top.ne
  have hDle : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨(D.toReal + 1) * B, mul_pos (by positivity) hB, ?_⟩
  intro h hh hhone f hcut s
  have H := OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_of_weighted_time_domination hp OAI.Analysis.Fourier.BochnerRiesz.measurable_timeDensity OAI.Analysis.Fourier.BochnerRiesz.timeDensity_le_one
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f)).measurable
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_thinShellCycles_space φ 1 f s).aestronglyMeasurable (ha n f s)
  have HF : eLpNorm (fun x ↦ OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((D.toReal + 1) * B * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ D * eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1))
          (ENNReal.ofReal p) (volume.prod volume) := H
      _ ≤ ENNReal.ofReal (D.toReal + 1) *
          (ENNReal.ofReal (B * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
            eLpNorm f (ENNReal.ofReal p) volume) :=
        mul_le_mul' hDle (hb h hh hhone f hcut).2
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  exact ⟨HF.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (f.memLp _ volume).eLpNorm_lt_top), HF⟩

end OAI.MeasureTheory.Kakeya
