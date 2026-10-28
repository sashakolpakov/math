import Mathlib.Analysis.Complex.MeanValue

/-! # Circle Mean -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.CircleMean

noncomputable section

/-! The actual circle mean of a holomorphic function along every complex line through the center of a norm ball. -/

open Set _root_.Metric Real
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphic_line_circle_mean (f : E → ℂ) {R : ℝ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) (z : E) (hz : ‖z‖ < R) :
    circleAverage (fun c : ℂ => f (c • z)) 0 1 = f 0 := by
  have hmap : MapsTo (fun c : ℂ => c • z) (closedBall 0 |(1 : ℝ)|) (ball 0 R) := by
    intro c hc
    have hcn : ‖c‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right, abs_one] using hc
    rw [mem_ball, dist_zero_right, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg z) hcn).trans_lt hz
  have hcont : ContinuousOn (fun c : ℂ => f (c • z)) (closedBall 0 |(1 : ℝ)|) :=
    hf.2.comp (continuous_id.smul continuous_const).continuousOn (fun c hc => subset_closure (hmap hc))
  have hdiff : ∀ c ∈ ball (0 : ℂ) |(1 : ℝ)| \ (∅ : Set ℂ), DifferentiableAt ℂ (fun w => f (w • z)) c := by
    intro c hc
    have hcz := hmap (ball_subset_closedBall hc.1)
    exact ((hf.1 _ hcz).differentiableAt (isOpen_ball.mem_nhds hcz)).comp c (differentiableAt_id.smul_const z)
  simpa only [zero_smul] using circleAverage_of_differentiable_on_off_countable countable_empty hcont hdiff

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.CircleMean
