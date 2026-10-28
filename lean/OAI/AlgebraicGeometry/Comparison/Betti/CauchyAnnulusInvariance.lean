import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedCauchy
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Cauchy Annulus Invariance -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CauchyAnnulusInvariance.Dolbeault

noncomputable section

section

/-! The normalized Cauchy circle transform of a holomorphic function on
the punctured line is unchanged when the contour moves past no pole. -/

open _root_.Complex Set _root_.Metric
open scoped _root_.Topology

def cauchyCircleTransform (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ w in C(0, R), f w / (w - z)

theorem cauchyAnnulus_avoids_poles {r R : ℝ} (hr : 0 < r) {z w : ℂ}
    (hz : ‖z‖ < r ∨ R < ‖z‖) (hw : w ∈ closedBall 0 R \ ball 0 r) :
    w ≠ 0 ∧ w ≠ z := by
  have hwr : r ≤ ‖w‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hw.2
  have hwR : ‖w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hw.1
  constructor
  · intro h
    rw [h, norm_zero] at hwr
    exact (not_le_of_gt hr) hwr
  · intro h
    rw [h] at hwr hwR
    rcases hz with hz | hz
    · exact (not_le_of_gt hz) hwr
    · exact (not_le_of_gt hz) hwR

theorem cauchyCircleTransform_radius_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {z : ℂ}
    (hz : ‖z‖ < r ∨ R < ‖z‖) :
    cauchyCircleTransform f R z = cauchyCircleTransform f r z := by
  have hd (w : ℂ) (hw : w ∈ closedBall 0 R \ ball 0 r) :
      DifferentiableAt ℂ (fun v => f v / (v - z)) w := by
    obtain ⟨hw0, hwz⟩ := cauchyAnnulus_avoids_poles hr hz hw
    exact (hf.differentiableAt (PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen.mem_nhds hw0)).div
      (differentiableAt_id.sub_const z) (sub_ne_zero.mpr hwz)
  unfold cauchyCircleTransform
  apply congrArg (fun a : ℂ => (2 * Real.pi * I : ℂ)⁻¹ * a)
  apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
    (s := ∅) countable_empty
  · exact fun w hw => (hd w hw).continuousAt.continuousWithinAt
  · intro w hw
    exact hd w ⟨ball_subset_closedBall hw.1.1, fun h => hw.1.2 (ball_subset_closedBall h)⟩

end

/-! Removing the evaluation pole from the Cauchy integrand by the actual
divided difference, including the circle integral outside that pole. -/

open _root_.Complex Set _root_.Metric
open scoped _root_.Topology

theorem circleIntegral_inv_eq_zero_outside {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : R < ‖z‖) :
    (∮ w in C(0, R), (w - z)⁻¹) = 0 := by
  have hd (w : ℂ) (hw : w ∈ closedBall 0 R) :
      DifferentiableAt ℂ (fun v => (v - z)⁻¹) w := by
    apply (differentiableAt_id.sub_const z).inv
    intro h
    have hwz := sub_eq_zero.mp h
    have hn : ‖w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hw
    exact (not_le_of_gt hz) (hwz ▸ hn)
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w (ball_subset_closedBall hw.1))

theorem circleIntegral_dslope_formula {f : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : ‖z‖ ≠ R) (hf : ContinuousOn f (sphere 0 R)) :
    (∮ w in C(0, R), dslope f z w) =
      (∮ w in C(0, R), f w / (w - z)) - (∮ w in C(0, R), (w - z)⁻¹) * f z := by
  have hne (w : ℂ) (hw : w ∈ sphere 0 R) : w ≠ z := by
    intro h
    apply hz
    simpa only [h, mem_sphere, dist_zero_right] using hw
  have hi : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere 0 R) := by
    intro w hw
    have hd : DifferentiableAt ℂ (fun v => (v - z)⁻¹) w :=
      (differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr (hne w hw))
    exact hd.continuousAt.continuousWithinAt
  have hg : CircleIntegrable (fun w => f w / (w - z)) 0 R :=
    (hf.div (continuousOn_id.sub continuousOn_const)
      (fun w hw => sub_ne_zero.mpr (hne w hw))).circleIntegrable hR
  have hk : CircleIntegrable (fun w : ℂ => (w - z)⁻¹ • f z) 0 R :=
    (hi.smul continuousOn_const).circleIntegrable hR
  calc
    _ = ∮ w in C(0, R), f w / (w - z) - (w - z)⁻¹ • f z := by
      apply circleIntegral.integral_congr hR
      intro w hw
      rw [dslope_of_ne f (hne w hw)]
      simp only [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul, mul_sub]
    _ = _ := by
      rw [circleIntegral.integral_sub hg hk, circleIntegral.integral_smul_const]
      rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.CauchyAnnulusInvariance.Dolbeault
