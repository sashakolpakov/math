import OAI.Analysis.Fourier.Radial.Sphere.Derivatives
import OAI.Analysis.Fourier.Radial.Curve

open OAI.Analysis.Fourier.Wave

/-! Transverse second derivatives of the sphere Fourier kernel. -/

open _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem norm_orthogonal_line {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : inner ℝ v w = 0) (r t : ℝ) :
    ‖r • v + t • w‖ = radialTransverseCurve r t := by
  have H : ‖r • v + t • w‖ ^ 2 = r ^ 2 + t ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hv, hw, mul_one,
      real_inner_smul_left, real_inner_smul_right, hvw, mul_zero, add_zero,
      sq_abs]
  calc
    _ = Real.sqrt (‖r • v + t • w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = radialTransverseCurve r t := congrArg Real.sqrt H

theorem sphereCosine_transverse_deriv {n : ℕ} {v w : Space n}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : inner ℝ v w = 0)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    sphereCosineLineDeriv (r • v) w t =
      sphereCosineLineDeriv 0 v (radialTransverseCurve r t) *
        (t / radialTransverseCurve r t) := by
  have H := (hasDerivAt_axisSphereCosineKernel v (radialTransverseCurve r t)).comp t
    (hasDerivAt_radialTransverseCurve hr t)
  have Heq : (fun s => sphereCosineKernel (r • v + s • w)) =
      (fun s => axisSphereCosineKernel v (radialTransverseCurve r s)) := by
    funext s
    rw [sphereCosineKernel_radial hv, norm_orthogonal_line hv hw hvw]
  apply (hasDerivAt_sphereCosineLine (r • v) w t).unique
  rw [Heq]
  exact H

theorem sphereCosine_transverse_second {n : ℕ} {v w : Space n}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : inner ℝ v w = 0)
    {r : ℝ} (hr : 0 < r) :
    sphereCosineLineSecond (r • v) w 0 = sphereCosineLineDeriv 0 v r / r := by
  have H := hasDerivAt_radialTransverseSecond hr
    (hasDerivAt_sphereCosineLineDeriv 0 v r)
  apply (hasDerivAt_sphereCosineLineDeriv (r • v) w 0).unique
  have Heq : sphereCosineLineDeriv (r • v) w =
      (fun t => sphereCosineLineDeriv 0 v (radialTransverseCurve r t) *
        (t / radialTransverseCurve r t)) := by
    funext t
    exact sphereCosine_transverse_deriv hv hw hvw hr t
  rw [Heq]
  exact H

end OAI.Analysis.Fourier.Radial
