import OAI.Analysis.PDE.Elliptic.Boundary.ScaledInterpolation

/-! The boundary interpolation remains uniform when the available interior
ball is only a fixed fraction of the boundary depth. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem fderiv_boundary_decay_on_smaller_ball
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E → V} {x : E} {h κ A B a b : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 < a) (hb : 0 < b)
    (hf : ∀ y ∈ closedBall x (κ * h / 2), DifferentiableAt ℝ f y)
    (hval : ∀ y ∈ closedBall x (κ * h / 2), ‖f y‖ ≤ A * h ^ (1 + a))
    (hder : ∀ y ∈ closedBall x (κ * h / 2),
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ B * (‖y - x‖ / h) ^ b) :
    ‖fderiv ℝ f x‖ ≤ (4 * A / κ ^ (1 + a) + B) * h ^ (a * b / (1 + b)) := by
  have hscale : 0 < κ * h := mul_pos hκ hh
  have hscaleh : κ * h ≤ h := mul_le_of_le_one_left hh.le hκ1
  have hscale1 : κ * h ≤ 1 := hscaleh.trans hh1
  have hkpow : 0 < κ ^ (1 + a) := Real.rpow_pos_of_pos hκ _
  have hp := fderiv_boundary_decay_of_scaled_holder hscale hscale1
    (show 0 ≤ A / κ ^ (1 + a) by positivity) hB ha hb hf
    (fun y hy => by
      have he : (A / κ ^ (1 + a)) * (κ * h) ^ (1 + a) = A * h ^ (1 + a) := by
        rw [Real.mul_rpow hκ.le hh.le]
        field_simp
      rw [he]
      exact hval y hy)
    (fun y hy => (hder y hy).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_left (norm_nonneg _) hscale hscaleh) hb.le) hB))
  have hγ : 0 ≤ a * b / (1 + b) := by positivity
  have hpow := Real.rpow_le_rpow hscale.le hscaleh hγ
  have hcoef : 0 ≤ 4 * (A / κ ^ (1 + a)) + B := by positivity
  apply hp.trans
  convert mul_le_mul_of_nonneg_left hpow hcoef using 1 ; ring

end OAI.Analysis.PDE.Elliptic
