import OAI.Analysis.PDE.WaveEquation.VelocitySymbol

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

theorem sqrt_one_add_sq_div_sub_one {r : ℝ} (hr : 0 < r) :
    Real.sqrt (1+r^2) / r - 1 = (r * (Real.sqrt (1+r^2) + r))⁻¹ := by
  have hs : 0 < Real.sqrt (1+r^2) := Real.sqrt_pos.2 (by positivity)
  have he := Real.sq_sqrt (show 0 ≤ 1+r^2 by positivity)
  field_simp
  nlinarith

theorem velocityShiftSymbol_eq {n : ℕ} {ξ : Space n} (hξ : 8 ≤ ‖ξ‖) :
    velocityShiftSymbol ξ = Real.sqrt (1+‖ξ‖^2) / ‖ξ‖ := by
  rw [velocityShiftSymbol, velocityHighSymbol_eq, velocityLowCutoff_zero hξ,
    sub_zero, ← Real.sqrt_eq_rpow]
  ring

theorem velocityShiftAnnulus_scaling {n : ℕ} {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (ξ : Space n) :
    ((velocityShiftSymbol ξ - 1 : ℝ) : ℂ) * OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (h • ξ) =
      (h^2 : ℝ) * velocityShiftAnnulus (h, h • ξ) := by
  by_cases hz : OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff (h • ξ) = 0
  · simp [velocityShiftAnnulus, hz]
  have hnorm : 8 < ‖h • ξ‖ := by
    by_contra! hle
    exact hz (OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff_eq_zero_of_norm_le_eight hle)
  have hξ : 8 < ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hnorm
    nlinarith [norm_nonneg ξ]
  have hs : h^2 + ‖h • ξ‖^2 = h^2 * (1+‖ξ‖^2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    ring
  have hsqrt : Real.sqrt (h^2 + ‖h • ξ‖^2) = h * Real.sqrt (1+‖ξ‖^2) := by
    rw [hs, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  rw [velocityShiftSymbol_eq hξ.le, sqrt_one_add_sq_div_sub_one (by linarith)]
  dsimp only [velocityShiftAnnulus]
  rw [hsqrt]
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos hh, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_add]
  push_cast
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hξC : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (show ‖ξ‖ ≠ 0 by linarith)
  have hsC : ((Real.sqrt (1+‖ξ‖^2) : ℝ) : ℂ) + (‖ξ‖ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, ne_eq, Complex.ofReal_eq_zero]
    linarith [Real.sqrt_nonneg (1+‖ξ‖^2)]
  field_simp


end OAI.Analysis.PDE.WaveEquation
