import OAI.Analysis.Fourier.Restriction.LocalCritical

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Evaluating a logarithmic loss at the polynomial observation radius still
costs only a logarithmic loss of the same degree. -/
theorem restrictionObservationRadius_log_bound (n k : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (1 + Real.log (OAI.Analysis.Fourier.Restriction.restrictionObservationRadius n R)) ^ k ≤
      ((n : ℝ) + 3 + Real.log (2 + Real.pi)) ^ k * (1 + Real.log R) ^ k := by
  have hR0 : 0 < R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlogC : 0 ≤ Real.log (2 + Real.pi) := Real.log_nonneg (by linarith [Real.pi_pos])
  have hid : Real.log (OAI.Analysis.Fourier.Restriction.restrictionObservationRadius n R) =
      Real.log (2 + Real.pi) + ((n : ℝ) + 2) * Real.log R := by
    rw [OAI.Analysis.Fourier.Restriction.restrictionObservationRadius, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    rfl
  rw [hid, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg hlogC hlogR]

/-- A quantitative far-field restriction estimate with logarithmic loss
implies the local critical restriction estimate, without an epsilon-removal
argument or any change in the logarithmic degree. -/
theorem logarithmic_local_restriction_of_farField {n k : ℕ} (hn : 2 ≤ n)
    {c D B : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hfar : ∀ R : ℝ, 0 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      (∀ y, R < ‖y‖ → f y = 0) → ∀ T : ℝ,
      2 ≤ T → 2 * R ≤ T → Real.pi / 2 ≤ T →
      ENNReal.ofReal c *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (B * (1 + Real.log T) ^ k) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume +
        ENNReal.ofReal (D * (1 + R ^ 2) / T * ∫ y, ‖f y‖) *
          OAI.Analysis.Fourier.Restriction.sphereMeasure n univ ^ (1 / OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f →
      MemLp f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume →
      (∀ y, R < ‖y‖ → f y = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal ((1 + Real.log R) ^ k) *
          eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.restrictionInputExponent n)) volume := by
  let p := OAI.Analysis.Fourier.Restriction.restrictionInputExponent n
  have hp : 1 < p := (OAI.Analysis.Fourier.Restriction.restrictionInputExponent_bounds hn).1
  have hp0 : 0 < p := by linarith
  let A := ENNReal.ofReal (B * ((n : ℝ) + 3 + Real.log (2 + Real.pi)) ^ k)
  let S := OAI.Analysis.Fourier.Restriction.sphereMeasure n univ ^ (1 / p)
  let V := volume (ball (0 : Space n) 1) ^ (1 - 1 / p)
  let E := ENNReal.ofReal D * V * S
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hs0 : 0 ≤ 1 - 1 / p := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le
    simpa only [div_one] using sub_nonneg.mpr hh
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs0
    (measure_ball_lt_top : volume (ball (0 : Space n) 1) < ⊤).ne
  have hS : S ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (measure_lt_top (OAI.Analysis.Fourier.Restriction.sphereMeasure n) univ).ne
  have hE : E ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hS
  refine ⟨(ENNReal.ofReal c)⁻¹ * (A + E),
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hE⟩), ?_⟩
  intro R hR f hfm hfi hfp hfs
  obtain ⟨hT, hRT, hpi⟩ := OAI.Analysis.Fourier.Restriction.restrictionObservationRadius_bounds n hR
  have H := hfar R (by linarith) f hfm hfi hfp hfs
    (OAI.Analysis.Fourier.Restriction.restrictionObservationRadius n R) hT hRT hpi
  have HE := OAI.Analysis.Fourier.Restriction.restriction_local_error_bound hfi hfs hR hp.le hD S
  change _ ≤ E * eLpNorm f (ENNReal.ofReal p) volume at HE
  have HA : ENNReal.ofReal (B * (1 + Real.log (OAI.Analysis.Fourier.Restriction.restrictionObservationRadius n R)) ^ k) ≤
      A * ENNReal.ofReal ((1 + Real.log R) ^ k) := by
    have hlogC : 0 ≤ Real.log (2 + Real.pi) := Real.log_nonneg (by linarith [Real.pi_pos])
    dsimp [A]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (restrictionObservationRadius_log_bound n k hR) hB
  have HQ : 1 ≤ ENNReal.ofReal ((1 + Real.log R) ^ k) :=
    ENNReal.one_le_ofReal.mpr (one_le_pow₀ (by linarith [Real.log_nonneg hR]))
  have HH : ENNReal.ofReal c *
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (A + E) * ENNReal.ofReal ((1 + Real.log R) ^ k) * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ A * ENNReal.ofReal ((1 + Real.log R) ^ k) * eLpNorm f (ENNReal.ofReal p) volume +
          E * eLpNorm f (ENNReal.ofReal p) volume :=
        H.trans (add_le_add (mul_le_mul' HA le_rfl) HE)
      _ ≤ A * ENNReal.ofReal ((1 + Real.log R) ^ k) * eLpNorm f (ENNReal.ofReal p) volume +
          (E * ENNReal.ofReal ((1 + Real.log R) ^ k)) * eLpNorm f (ENNReal.ofReal p) volume := by
        gcongr
        simpa only [mul_one] using mul_le_mul' (le_refl E) HQ
      _ = _ := by ring
  calc
    _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal c)⁻¹ * ((A + E) * ENNReal.ofReal ((1 + Real.log R) ^ k) *
        eLpNorm f (ENNReal.ofReal p) volume) := mul_le_mul' le_rfl HH
    _ = _ := by ring

end OAI.MeasureTheory.Kakeya
