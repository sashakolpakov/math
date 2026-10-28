import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Endpoints
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.High

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem finite_constant_majorant {A : ℝ≥0∞} (hA : A ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ A ≤ .ofReal C := by
  refine ⟨A.toReal+1,by positivity,?_⟩
  calc
    A = .ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

theorem frequency_bound_below_critical {n : ℕ} (hn : 2 ≤ n) {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (E : FrequencyEndpoints n φ)
    {p : ℝ} (hp : 2 < p) (hpq : p < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
  obtain ⟨D,hD,hKD⟩ := finite_constant_majorant
    (finiteInterpolationConstant_ne_top (q₀ := 2) (q₁ := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) (by linarith : 0 < p))
  refine ⟨D*(E.twoConstant+E.criticalConstant),mul_pos hD (add_pos E.two_pos E.critical_pos),?_⟩
  intro h hh h1 f
  let L := 1+Real.log (1/h)
  have hL : 1 ≤ L := logarithm_weight_one_le hh h1
  have hpow : 1 ≤ L ^ (2*n+5) := one_le_pow₀ hL
  have hpw : 0 < L ^ (2*n+5) := lt_of_lt_of_le zero_lt_one hpow
  let M := (E.twoConstant+E.criticalConstant)*L^(2*n+5)
  have hM : 0 < M := mul_pos (add_pos E.two_pos E.critical_pos) hpw
  have h2M : E.twoConstant ≤ M := by
    calc
      _ ≤ E.twoConstant+E.criticalConstant := le_add_of_nonneg_right E.critical_pos.le
      _ ≤ M := le_mul_of_one_le_right (add_pos E.two_pos E.critical_pos).le hpow
  have hcM : E.criticalConstant*L^(2*n+5) ≤ M :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left E.two_pos.le) hpw.le
  have H := operator_common_endpoint_bound volume (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)
    (fun g z => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
    (fun g hg hi => measurable_frequencyWave hφ hs hh hg hi)
    (fun g k hg hk z => frequencyHalfWave_add hφ hs hh z.2 hg hk z.1)
    (by norm_num : (0:ℝ)<2) hp hpq hM
    (fun g hg hi h2 _ => by
      have H2 := E.two h hh h1 g hg hi (by simpa using h2)
      exact (by simpa using H2 : eLpNorm (fun z : Space n × ℝ => frequencyHalfWave φ h z.2 g z.1)
        (.ofReal 2) (observationMeasure n) ≤ .ofReal E.twoConstant * eLpNorm g (.ofReal 2) volume).trans
          (mul_le_mul' (ENNReal.ofReal_le_ofReal h2M) le_rfl))
    (fun g hg hi _ hq => (E.critical h hh h1 g hg hi hq).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hcM) le_rfl))
    f.continuous.measurable f.integrable (f.memLp _ volume) (f.memLp _ volume)
  have hcoef : finiteInterpolationConstant 2 p (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) * .ofReal M ≤
      .ofReal (D*(E.twoConstant+E.criticalConstant)*L^(2*n+5)) := by
    calc
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal M := mul_le_mul' hKD le_rfl
      _ = _ := by rw [← ENNReal.ofReal_mul hD.le]; congr 1; dsimp [M]; ring
  have H' := H.trans (mul_le_mul' hcoef le_rfl)
  simpa only [smoothingOrder_of_le_critical hn (by linarith) hpq.le,
    neg_zero, Real.rpow_zero, mul_one, L] using H'

theorem frequency_bound_above_critical {n : ℕ} (hn : 2 ≤ n) {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (E : FrequencyEndpoints n φ)
    {p : ℝ} (hqp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
  have hq : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := lt_trans (by norm_num) (criticalExponent_gt_two hn)
  have hp : 0 < p := hq.trans hqp
  let θ := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n/p
  have ht : 0 ≤ θ := div_nonneg hq.le hp.le
  have ht1 : θ ≤ 1 := (div_le_one hp).mpr hqp.le
  obtain ⟨D,hD,hKD⟩ := finite_constant_majorant (infinityInterpolationConstant_ne_top (q := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) hp)
  let C := D * (E.criticalConstant^θ * E.infinityConstant^(1-θ))
  have hC : 0 < C := mul_pos hD (mul_pos (Real.rpow_pos_of_pos E.critical_pos _)
    (Real.rpow_pos_of_pos E.infinity_pos _))
  refine ⟨C,hC,?_⟩
  intro h hh h1 f
  let L := 1+Real.log (1/h)
  have hL : 1 ≤ L := logarithm_weight_one_le hh h1
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have H := operator_finite_infinity_bound volume (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)
    (fun g z => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
    (fun g hg hi => measurable_frequencyWave hφ hs hh hg hi)
    (fun g k hg hk z => frequencyHalfWave_add hφ hs hh z.2 hg hk z.1)
    hq hqp (mul_pos E.critical_pos (pow_pos hLp _))
    (mul_pos E.infinity_pos (Real.rpow_pos_of_pos hh _))
    (fun g hg hi hqg => E.critical h hh h1 g hg hi hqg)
    (fun g hg hi M hM hb => E.infinity h hh h1 g hg hi M hM hb)
    f.continuous.measurable f.integrable (f.memLp _ volume)
  have hb := interpolation_factor_le (a := -((n:ℝ)-1)/2) (k := 2*n+5)
    E.critical_pos E.infinity_pos hL hh ht ht1
  rw [high_frequency_exponent hn hqp.le] at hb
  have hc : infinityInterpolationConstant (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) p *
      .ofReal ((E.criticalConstant*L^(2*n+5))^θ *
        (E.infinityConstant*h^(-((n:ℝ)-1)/2))^(1-θ)) ≤
      .ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*L^(2*n+5)) := by
    calc
      _ ≤ .ofReal D * .ofReal ((E.criticalConstant^θ*E.infinityConstant^(1-θ))*
          h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*L^(2*n+5)) := mul_le_mul' hKD (ENNReal.ofReal_le_ofReal hb)
      _ = _ := by rw [← ENNReal.ofReal_mul hD.le]; congr 1; dsimp [C]; ring
  exact H.trans (mul_le_mul' hc le_rfl)

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
