import OAI.Analysis.PDE.Concentration.DirichletComparison
import OAI.Analysis.PDE.Concentration.BarrierDeterminant
import OAI.Analysis.PDE.Dirichlet.Translation

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem quaternionHessian_three_norm_sq {n : ℕ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 => ‖y‖ ^ 2) x =
      (6 : ℝ) • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) := by
  have he (α : Fin 3) : OAI.Analysis.Calculus.Quaternion.threeSlots α * star (OAI.Analysis.Calculus.Quaternion.threeSlots α) = 1 := by
    fin_cases α <;> ext <;> norm_num [OAI.Analysis.Calculus.Quaternion.threeSlots, Quaternion.re_mul]
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian
  rw [OAI.Analysis.PDE.Dirichlet.realHessian_norm_sq, OAI.Analysis.Calculus.Quaternion.hessianMap_smul, OAI.Analysis.PDE.Dirichlet.hessianMap_one OAI.Analysis.Calculus.Quaternion.threeSlots he]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

theorem quaternionHessian_three_ball {n : ℕ} (x₀ x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3) (h : ℝ) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => ‖y - x₀‖ ^ 2 - h ^ 2) x =
      (6 : ℝ) • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) := by
  have ht : (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 => ‖y - x₀‖ ^ 2) =
      (fun y => ‖-x₀ + y‖ ^ 2) := by ext y; rw [sub_eq_add_neg, add_comm]
  have hc : ContDiff ℝ 2 (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 => ‖y - x₀‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have he : (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 => ‖y - x₀‖ ^ 2 - h ^ 2) =
      (fun y => ‖y - x₀‖ ^ 2 + (-1 : ℝ) • h ^ 2) := by ext y; simp only [smul_eq_mul]; ring
  rw [he, OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.threeSlots hc contDiff_const,
    OAI.Analysis.PDE.Dirichlet.quaternionHessian_const, smul_zero, add_zero, ht]
  exact (OAI.Analysis.PDE.Dirichlet.quaternionHessian_translation OAI.Analysis.Calculus.Quaternion.threeSlots (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 => ‖y‖ ^ 2)
    (-x₀) x).trans (quaternionHessian_three_norm_sq _)

/-- Local comparison with the actual quadratic ball barrier. Only interior
C² and continuity up to the ball boundary are required. -/
theorem ball_barrier_comparison {n : ℕ} (hn : 1 ≤ n)
    (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3) (h α : ℝ) (hh : 0 < h)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 → ℝ}
    (hB : ContDiffOn ℝ 2 B (Metric.ball x₀ h))
    (hu : ContDiffOn ℝ 2 u (Metric.ball x₀ h))
    (hBc : ContinuousOn B (Metric.closedBall x₀ h))
    (huc : ContinuousOn u (Metric.closedBall x₀ h))
    (hpos : ∀ x ∈ Metric.ball x₀ h,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => B y + u y) x)).PosDef)
    (hdet : ∀ x ∈ Metric.ball x₀ h,
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + α * (‖y - x₀‖ ^ 2 - h ^ 2)) x) ≤
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => B y + u y) x))
    (hbd : ∀ x, ‖x - x₀‖ = h → u x ≤ 0) :
    ∀ x ∈ Metric.closedBall x₀ h, u x ≤ α * (‖x - x₀‖ ^ 2 - h ^ 2) := by
  let r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 3 → ℝ := fun x => ‖x - x₀‖ ^ 2 - h ^ 2
  have hr : ContDiff ℝ 2 r :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  have hb : {x | r x < 0} = Metric.ball x₀ h := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, r, sub_lt_zero]
    exact sq_lt_sq₀ (norm_nonneg _) hh.le
  have hcb : {x | r x ≤ 0} = Metric.closedBall x₀ h := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm, r, sub_nonpos]
    exact sq_le_sq₀ (norm_nonneg _) hh.le
  have hcomp := slots_dirichlet_comparison_representatives hn OAI.Analysis.Calculus.Quaternion.threeSlots
    (r := r) (f := fun y => B y + u y) (g := fun y => B y + α * r y)
    (K := Metric.closedBall x₀ h) id (isCompact_closedBall x₀ h)
    (by rw [hcb]) (by rw [hb]; exact hB.add hu)
    (by rw [hb]; exact hB.add (contDiffOn_const.mul hr.contDiffOn)) hr
    (by rw [hcb]; exact hBc.add huc)
    (by rw [hcb]; exact hBc.add (continuousOn_const.mul hr.continuous.continuousOn))
    (by intro x hx; exact hcb ▸ hx) (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by
      intro x hx
      rw [quaternionHessian_three_ball]
      rw [OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
      exact (Matrix.PosDef.one).smul (by norm_num))
    (by
      intro x hx
      have hx' : x ∈ {x | r x < 0} := hx
      rw [hb] at hx'
      exact hpos x hx')
    (by
      intro x hx
      have hx' : x ∈ {x | r x < 0} := hx
      rw [hb] at hx'
      exact hdet x hx')
    (by
      intro x hx
      have he : ‖x - x₀‖ = h := (sq_eq_sq₀ (norm_nonneg _) hh.le).mp (sub_eq_zero.mp hx)
      have hu0 := hbd x he
      dsimp only [r] at hx ⊢
      rw [hx, mul_zero]
      linarith)
  intro x hx
  have hx' : x ∈ {x | r x ≤ 0} := hcb.symm ▸ hx
  have hi := hcomp x hx'
  exact (add_le_add_iff_left (B x)).mp hi

end OAI.Analysis.PDE.Concentration
