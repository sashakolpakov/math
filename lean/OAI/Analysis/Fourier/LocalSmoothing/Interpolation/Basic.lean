import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Bounds

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

/-- The critical logarithmic estimate implies the sharp frequency-localized
bound at every finite p ≥ 2. All endpoint and interpolation inputs are proved. -/
theorem frequency_bound_of_logarithmicRefinement (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 2 ≤ p) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
  obtain ⟨E⟩ := frequency_endpoints_of_logarithmicRefinement hlog hn hφ hs hz
  have Hb : ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
    rcases eq_or_lt_of_le hp with rfl | hp
    · refine ⟨E.twoConstant,E.two_pos,?_⟩
      intro h hh h1 f
      have H := E.two h hh h1 f f.continuous.measurable f.integrable (f.memLp _ volume)
      have hweight : 1 ≤ (1+Real.log (1/h))^(2*n+5) := one_le_pow₀ (logarithm_weight_one_le hh h1)
      have hc : E.twoConstant ≤ E.twoConstant*(1+Real.log (1/h))^(2*n+5) :=
        le_mul_of_one_le_right E.two_pos.le hweight
      simpa only [ENNReal.ofReal_ofNat,OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder_two,neg_zero,Real.rpow_zero,mul_one] using
        H.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl)
    · rcases lt_trichotomy p (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) with hpq | rfl | hqp
      · exact frequency_bound_below_critical hn hφ.continuous hs E hp hpq
      · refine ⟨E.criticalConstant,E.critical_pos,?_⟩
        intro h hh h1 f
        simpa only [smoothingOrder_of_le_critical hn (by linarith [criticalExponent_gt_two hn]) le_rfl,
          neg_zero,Real.rpow_zero,mul_one] using
          E.critical h hh h1 f f.continuous.measurable f.integrable (f.memLp _ volume)
      · exact frequency_bound_above_critical hn hφ.continuous hs E hqp
  obtain ⟨C,hC,hb⟩ := Hb
  refine ⟨C,hC,?_⟩
  intro h hh h1 f
  have H := hb h hh h1 f
  refine ⟨H.trans_lt ?_,H⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
