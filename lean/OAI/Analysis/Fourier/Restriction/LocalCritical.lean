import OAI.Analysis.Fourier.Restriction.CriticalInput
import OAI.Analysis.Fourier.Restriction.LocalError

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Local smoothing gives the critical diagonal restriction estimate on each
spatial ball, with an arbitrarily small power of its radius. -/
theorem localSmoothing_local_restriction_critical (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → MemLp f (ENNReal.ofReal (restrictionInputExponent n)) volume →
      (∀ x, R < ‖x‖ → f x = 0) →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (restrictionInputExponent n)) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume := by
  let p := restrictionInputExponent n
  have hp : 1 < p := (restrictionInputExponent_bounds hn).1
  have hp0 : 0 < p := by linarith
  let δ := ε / ((n : ℝ) + 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : ((n : ℝ) + 2) * δ = ε := by
    dsimp [δ]
    field_simp
  obtain ⟨c, D, B, hc, hD, hB, H⟩ := bochnerRiesz_critical_farField hls hn hδ
  let A := ENNReal.ofReal (B * (2 + Real.pi) ^ δ)
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
  have hR0 : 0 < R := by linarith
  obtain ⟨hT, hRT, hpi⟩ := restrictionObservationRadius_bounds n hR
  have H := H R hR0.le f hfm hfi hfp hfs (restrictionObservationRadius n R) hT hRT hpi
  have HE := restriction_local_error_bound hfi hfs hR hp.le hD S
  change _ ≤ E * eLpNorm f (ENNReal.ofReal p) volume at HE
  rw [restrictionObservationRadius_power n hR0 δ, hδε] at H
  have hmain : ENNReal.ofReal (B * ((2 + Real.pi) ^ δ * R ^ ε)) =
      A * ENNReal.ofReal (R ^ ε) := by
    dsimp [A]
    rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
  rw [hmain] at H
  have HQ : 1 ≤ ENNReal.ofReal (R ^ ε) :=
    ENNReal.one_le_ofReal.mpr (Real.one_le_rpow hR hε.le)
  have HH : ENNReal.ofReal c *
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (A + E) * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ A * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal p) volume +
          E * eLpNorm f (ENNReal.ofReal p) volume := H.trans (add_le_add le_rfl HE)
      _ ≤ A * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal p) volume +
          (E * ENNReal.ofReal (R ^ ε)) * eLpNorm f (ENNReal.ofReal p) volume := by
        gcongr
        simpa only [mul_one] using mul_le_mul' (le_refl E) HQ
      _ = _ := by ring
  calc
    _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c *
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal c)⁻¹ * ((A + E) * ENNReal.ofReal (R ^ ε) *
        eLpNorm f (ENNReal.ofReal p) volume) := mul_le_mul' le_rfl HH
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
