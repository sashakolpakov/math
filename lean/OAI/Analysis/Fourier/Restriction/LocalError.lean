import OAI.Analysis.Fourier.Restriction.CompactNorm
import OAI.Analysis.Fourier.Restriction.ObservationRadius

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem restriction_local_error_bound {n : ℕ} {f : Space n → ℂ} {R p D : ℝ}
    (hf : Integrable f) (hs : ∀ x, R < ‖x‖ → f x = 0)
    (hR : 1 ≤ R) (hp : 1 ≤ p) (hD : 0 ≤ D) (S : ℝ≥0∞) :
    ENNReal.ofReal (D * (1 + R ^ 2) / restrictionObservationRadius n R * ∫ y, ‖f y‖) * S ≤
      ENNReal.ofReal D * volume (ball (0 : Space n) 1) ^ (1 - 1 / p) * S *
        eLpNorm f (ENNReal.ofReal p) volume := by
  have hT : 0 < restrictionObservationRadius n R := by
    have := (restrictionObservationRadius_bounds n hR).1
    linarith
  have he : D * (1 + R ^ 2) / restrictionObservationRadius n R * R ^ n ≤ D := by
    calc
      _ = D * ((1 + R ^ 2) / restrictionObservationRadius n R * R ^ n) := by ring
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left (restrictionObservationRadius_error n hR) hD
      _ = D := mul_one D
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ D * (1 + R ^ 2) / restrictionObservationRadius n R)]
  calc
    _ ≤ ENNReal.ofReal (D * (1 + R ^ 2) / restrictionObservationRadius n R) *
        (ENNReal.ofReal (R ^ n) * volume (ball (0 : Space n) 1) ^ (1 - 1 / p) *
          eLpNorm f (ENNReal.ofReal p) volume) * S := by
      gcongr
      exact integral_norm_le_compact_Lp_polynomial hf hs hR hp
    _ = (ENNReal.ofReal (D * (1 + R ^ 2) / restrictionObservationRadius n R) *
        ENNReal.ofReal (R ^ n)) *
        (volume (ball (0 : Space n) 1) ^ (1 - 1 / p) * S * eLpNorm f (ENNReal.ofReal p) volume) := by ring
    _ ≤ ENNReal.ofReal D *
        (volume (ball (0 : Space n) 1) ^ (1 - 1 / p) * S * eLpNorm f (ENNReal.ofReal p) volume) := by
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal he
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
