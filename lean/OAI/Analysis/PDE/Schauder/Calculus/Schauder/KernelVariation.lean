import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelDerivative

/-! The far-field variation bound for the genuine Newtonian Hessian kernel. -/

noncomputable section
open Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem newtonianEntry_difference_bound (m : ℕ) (v w : E) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : E, x ≠ 0 → ‖y - x‖ ≤ ‖x‖ / 2 →
      |newtonianEntry m v w y - newtonianEntry m v w x| ≤
        C * (‖x‖ / 2) ^ (-(m : ℝ) - 1) * ‖y - x‖ := by
  obtain ⟨C, hC, hbound⟩ := newtonianEntry_fderiv_decay m v w
  refine ⟨C, hC, ?_⟩
  intro x y hx hxy
  have hxpos : 0 < ‖x‖ / 2 := half_pos (norm_pos_iff.mpr hx)
  have hnorm (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) : ‖x‖ / 2 ≤ ‖z‖ := by
    have ht : ‖x‖ ≤ ‖z - x‖ + ‖z‖ := by
      have h := norm_add_le (x - z) z
      rw [sub_add_cancel, norm_sub_rev] at h
      exact h
    have hd : ‖z - x‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    linarith
  have hnz (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) : z ≠ 0 :=
    norm_pos_iff.mp (hxpos.trans_le (hnorm z hz))
  have hder (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) :
      DifferentiableAt ℝ (newtonianEntry m v w) z :=
    (contDiffAt_newtonianEntry m v w (hnz z hz)).differentiableAt (by norm_num)
  have hderbound (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) :
      ‖fderiv ℝ (newtonianEntry m v w) z‖ ≤ C * (‖x‖ / 2) ^ (-(m : ℝ) - 1) := by
    apply (hbound z (hnz z hz)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_nonpos hxpos (hnorm z hz)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hy : y ∈ closedBall x (‖x‖ / 2) := by
    simpa only [mem_closedBall, dist_eq_norm] using hxy
  have hi := Convex.norm_image_sub_le_of_norm_fderiv_le hder hderbound
    (convex_closedBall x (‖x‖ / 2)) (mem_closedBall_self hxpos.le) hy
  simpa only [Real.norm_eq_abs] using hi

end OAI.Analysis.PDE.Schauder
