import Mathlib

/-! The transverse second derivative of a radial profile, computed along
an ordinary real-variable curve rather than through polar coordinates. -/

open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

def radialTransverseCurve (r t : ℝ) : ℝ := Real.sqrt (r ^ 2 + t ^ 2)

theorem radialTransverseCurve_pos {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < radialTransverseCurve r t := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])

theorem radialTransverseCurve_zero {r : ℝ} (hr : 0 < r) :
    radialTransverseCurve r 0 = r := by
  simp only [radialTransverseCurve, sq, zero_mul, add_zero, Real.sqrt_mul_self hr.le]

theorem hasDerivAt_radialTransverseCurve {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasDerivAt (radialTransverseCurve r) (t / radialTransverseCurve r t) t := by
  have H := (((hasDerivAt_id t).pow 2).const_add (r ^ 2)).sqrt
    (by nlinarith [sq_nonneg t] : r ^ 2 + t ^ 2 ≠ 0)
  unfold radialTransverseCurve
  convert H using 1
  · rfl
  · change t / Real.sqrt (r ^ 2 + t ^ 2) =
      (2 : ℝ) * t ^ (2 - 1 : ℕ) * 1 / (2 * Real.sqrt (r ^ 2 + t ^ 2))
    norm_num
    ring

theorem hasDerivAt_radialTransverseSlope {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => t / radialTransverseCurve r t) (1 / r) 0 := by
  have H := (hasDerivAt_id (0 : ℝ)).div (hasDerivAt_radialTransverseCurve hr 0)
    (radialTransverseCurve_pos hr 0).ne'
  change HasDerivAt (fun t => t / radialTransverseCurve r t)
    ((1 * radialTransverseCurve r 0 - 0 * (0 / radialTransverseCurve r 0)) /
      radialTransverseCurve r 0 ^ 2) 0 at H
  convert H using 1
  rw [radialTransverseCurve_zero hr]
  field_simp
  ; ring

theorem hasDerivAt_radialTransverseSecond {r h : ℝ} {g : ℝ → ℝ}
    (hr : 0 < r) (hg : HasDerivAt g h r) :
    HasDerivAt (fun t => g (radialTransverseCurve r t) * (t / radialTransverseCurve r t))
      (g r / r) 0 := by
  have hq : HasDerivAt (radialTransverseCurve r) 0 0 := by
    simpa only [zero_div] using hasDerivAt_radialTransverseCurve hr 0
  have hgq : HasDerivAt (fun t => g (radialTransverseCurve r t)) 0 0 := by
    have hg' : HasDerivAt g h (radialTransverseCurve r 0) := by
      simpa only [radialTransverseCurve_zero hr] using hg
    have H := hg'.comp 0 hq
    simpa only [radialTransverseCurve_zero hr, mul_zero, Function.comp_def] using H
  have H := hgq.mul (hasDerivAt_radialTransverseSlope hr)
  change HasDerivAt (fun t => g (radialTransverseCurve r t) * (t / radialTransverseCurve r t))
    (0 * (0 / radialTransverseCurve r 0) + g (radialTransverseCurve r 0) * (1 / r)) 0 at H
  simpa only [zero_mul, add_zero, zero_div, radialTransverseCurve_zero hr,
    zero_add, mul_one_div] using H

end OAI.Analysis.Fourier.Radial
