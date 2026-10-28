import OAI.Analysis.Fourier.BesselPotential.SchwartzMultiplier
import OAI.Analysis.Fourier.BesselPotential.SchwartzGrowth

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped ContDiff ENNReal

namespace OAI.Analysis.Fourier.BesselPotential

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem temperate_log_bessel_weight (s B : ℝ) :
    (fun ξ : H => (1+‖ξ‖^2)^(s/2) *
      Real.log (2+Real.sqrt (1+‖ξ‖^2))^B).HasTemperateGrowth := by
  have hroot : (fun ξ : H => Real.sqrt (1+‖ξ‖^2)).HasTemperateGrowth := by
    simpa only [Real.sqrt_eq_rpow] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow H (1/2)
  have hbase : (fun ξ : H => 2+Real.sqrt (1+‖ξ‖^2)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const 2).add hroot
  have hthree (ξ : H) : 3 ≤ 2+Real.sqrt (1+‖ξ‖^2) := by
    have h : Real.sqrt 1 ≤ Real.sqrt (1+‖ξ‖^2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ‖ξ‖))
    norm_num only [Real.sqrt_one] at h
    linarith
  have hlog := temperate_log_of_one_le hbase (fun ξ => by linarith [hthree ξ])
  have hlower (ξ : H) : (1:ℝ)/2 < Real.log (2+Real.sqrt (1+‖ξ‖^2)) := by
    have h₁ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3)
    have h₂ : Real.log 3 ≤ Real.log (2+Real.sqrt (1+‖ξ‖^2)) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < 2+Real.sqrt (1+‖ξ‖^2) by positivity) (hthree ξ)
    norm_num at h₁
    linarith
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow H (s/2)).mul
    (temperate_rpow_of_half_lt hlog hlower B)

/-- The exact log-Bessel potential as a Schwartz function, for arbitrary
real differential order and arbitrary real logarithmic exponent. -/
def logBesselPotentialSchwartz {n : ℕ} (s B : ℝ)
    (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  angularSchwartzMultiplier (fun ξ => (1+‖ξ‖^2)^(s/2) *
    Real.log (2+Real.sqrt (1+‖ξ‖^2))^B) f

theorem logBesselPotentialSchwartz_eq {n : ℕ} (s B : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    (logBesselPotentialSchwartz s B f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f := by
  funext x
  exact angularSchwartzMultiplier_eq_integral (temperate_log_bessel_weight s B) f x

theorem angularFourier_logBesselPotential {n : ℕ} (s B : ℝ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) ξ =
      ((1+‖ξ‖^2)^(s/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B : ℝ) •
        OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  rw [← logBesselPotentialSchwartz_eq]
  exact angularFourier_angularSchwartzMultiplier (temperate_log_bessel_weight s B) f ξ

theorem memLp_logBesselPotential {n : ℕ} (s B : ℝ)
    (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    MemLp (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) p volume := by
  rw [← logBesselPotentialSchwartz_eq]
  exact (logBesselPotentialSchwartz s B f).memLp p

end OAI.Analysis.Fourier.BesselPotential
