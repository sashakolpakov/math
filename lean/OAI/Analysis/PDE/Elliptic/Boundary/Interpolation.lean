import Mathlib

/-! A quantitative derivative interpolation estimate. Small values together
with a Hölder modulus for the derivative force a small actual derivative. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem fderiv_norm_le_of_holder_remainder
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E → V} {x : E} {t A K b : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hf : ∀ y ∈ closedBall x t, DifferentiableAt ℝ f y)
    (hval : ∀ y ∈ closedBall x t, ‖f y‖ ≤ A)
    (hder : ∀ y ∈ closedBall x t,
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ K * ‖y - x‖ ^ b) :
    ‖fderiv ℝ f x‖ ≤ 2 * A / t + K * t ^ b := by
  have hx : x ∈ closedBall x t := mem_closedBall_self ht.le
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let z := x + t • v
  have hzx : z - x = t • v := by dsimp [z]; abel
  have hn : ‖z - x‖ = t := by rw [hzx, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  have hz : z ∈ closedBall x t := by
    simpa only [mem_closedBall, dist_eq_norm, hn] using (le_rfl : t ≤ t)
  have hr := Convex.norm_image_sub_le_of_norm_fderiv_le' hf
    (fun y hy => (hder y hy).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa only [mem_closedBall, dist_eq_norm] using hy) hb) hK))
    (convex_closedBall x t) hx hz
  rw [hn] at hr
  have hvv : ‖f z - f x‖ ≤ 2 * A :=
    (norm_sub_le _ _).trans (by linarith [hval z hz, hval x hx])
  have hd : ‖fderiv ℝ f x (z - x)‖ ≤ 2 * A + K * t ^ b * t := by
    have he : fderiv ℝ f x (z - x) = (f z - f x) - (f z - f x - fderiv ℝ f x (z - x)) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hvv hr)
  rw [hzx, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hd
  calc
    ‖fderiv ℝ f x v‖ ≤ (2 * A + K * t ^ b * t) / t :=
      (le_div_iff₀ ht).2 (by nlinarith)
    _ = 2 * A / t + K * t ^ b := by field_simp

end OAI.Analysis.PDE.Elliptic
