import OAI.Analysis.PDE.Concentration.RankConcentrationCoefficient
import OAI.Analysis.PDE.Concentration.BallBarrier
import OAI.Analysis.PDE.Concentration.SpatialBarrier

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

/-- The analytic comparison step for the rank-dependent determinant
estimate. The algebraic scalar-shift bound is discharged by the rank
theorem in `RankConcentration`. -/
theorem rank_concentration_of_scalar_shift_bound (m r : ℕ) (hr : r < m)
    {C₀ : ℝ} (hC : 0 ≤ C₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) (ρ lam m₀ : ℝ),
      0 < ρ → 0 < lam → 0 < m₀ → m₀ ≤ lam ^ (m-r) →
      ∀ (B u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 → ℝ),
      ContDiffOn ℝ 2 B (Metric.ball x₀ ρ) → ContDiffOn ℝ 2 u (Metric.ball x₀ ρ) →
      ContinuousOn B (Metric.closedBall x₀ ρ) → ContinuousOn u (Metric.closedBall x₀ ρ) →
      (∀ x ∈ Metric.ball x₀ ρ, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + u y) x)).PosDef) →
      (∀ x ∈ Metric.ball x₀ ρ, ∀ a : ℝ, 0 ≤ a →
        OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x + a • 1) ≤
          (C₀*lam+a)^r*a^(m-r)) →
      (∀ x ∈ Metric.ball x₀ ρ, OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + u y) x) = lam^r * μ x) →
      (∀ x ∈ Metric.ball x₀ ρ, m₀ ≤ μ x) →
      (∀ x, ‖x-x₀‖ = ρ → u x ≤ 0) →
      c*ρ^2*m₀^(1+1/((m-r:ℕ):ℝ)) ≤ (-u x₀)*μ x₀ := by
  obtain ⟨c,hc,-,hcoef⟩ := exists_rank_barrier_coefficient m r hr hC
  refine ⟨c,hc,?_⟩
  intro x₀ ρ lam m₀ hρ hlam hm₀ hml B u μ hB hu hBc huc hpos hshift hPDE hμ hbd
  let α := c*m₀^(1/((m-r:ℕ):ℝ))
  have hα : 0 ≤ α := mul_nonneg hc.le (Real.rpow_nonneg hm₀.le _)
  have hcoef' := (hcoef lam m₀ hlam hm₀.le hml).2
  have hdet (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) (hx : x ∈ Metric.ball x₀ ρ) :
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + α*(‖y-x₀‖^2-ρ^2)) x) ≤
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => B y + u y) x) := by
    have hb : ContDiffAt ℝ 2 B x := hB.contDiffAt (Metric.isOpen_ball.mem_nhds hx)
    have hq : ContDiffAt ℝ 2 (fun y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 => ‖y-x₀‖^2-ρ^2) x :=
      (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const).contDiffAt
    have he := quaternionHessian_linear_combination_at OAI.Analysis.Calculus.Quaternion.threeSlots hb hq 1 α
    simp only [one_mul,one_smul,quaternionHessian_three_ball,smul_smul] at he
    rw [he,hPDE x hx,mul_comm α 6]
    have hd := hshift x hx (6*α) (by positivity)
    apply (hd.trans hcoef').trans
    have hl : 0 ≤ lam^r := pow_nonneg hlam.le r
    have hμx := mul_le_mul_of_nonneg_left (hμ x hx) hl
    have hm : 0 ≤ lam^r*m₀ := mul_nonneg hl hm₀.le
    linarith
  have hb := ball_barrier_comparison (by omega) x₀ ρ α hρ hB hu hBc huc hpos hdet hbd
  have hx₀ : x₀ ∈ Metric.ball x₀ ρ := Metric.mem_ball_self hρ
  have hu₀ := hb x₀ (Metric.ball_subset_closedBall hx₀)
  simp only [sub_self,norm_zero,zero_pow (by omega : 2≠0),zero_sub] at hu₀
  have hneg : α*ρ^2 ≤ -u x₀ := by nlinarith
  have hμ₀ : m₀ ≤ μ x₀ := hμ x₀ hx₀
  calc
    c*ρ^2*m₀^(1+1/((m-r:ℕ):ℝ)) = α*ρ^2*m₀ := by
      rw [← rank_density_root_mul m r hm₀]
      dsimp only [α]
      ring
    _ ≤ α*ρ^2*μ x₀ := mul_le_mul_of_nonneg_left hμ₀ (by positivity)
    _ ≤ (-u x₀)*μ x₀ := mul_le_mul_of_nonneg_right hneg (hm₀.le.trans hμ₀)

end OAI.Analysis.PDE.Concentration
