import OAI.Analysis.PDE.Concentration.RankConcentrationComparison
import OAI.LinearAlgebra.Moore.MooreRankDeterminant

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

/-- The local concentration exponent for a background of arbitrary rank
`r < m`, as in the rank-extension appendix. The constant is chosen before
the ball, the density lower bound, the scale, and the potentials. Only
interior C² and continuity on the closed ball are needed. -/
theorem local_rank_concentration (m r : ℕ) (_ : 2 ≤ m) (hr : r < m)
    {C₀ : ℝ} (hC : 0 < C₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3) (ρ lam m₀ : ℝ),
      0 < ρ → 0 < lam → 0 < m₀ → m₀ ≤ lam ^ (m-r) →
      ∀ (B u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 → ℝ),
      ContDiffOn ℝ 2 B (Metric.ball x₀ ρ) → ContDiffOn ℝ 2 u (Metric.ball x₀ ρ) →
      ContinuousOn B (Metric.closedBall x₀ ρ) → ContinuousOn u (Metric.closedBall x₀ ρ) →
      (∀ x ∈ Metric.ball x₀ ρ,
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x)).PosSemidef) →
      (∀ x ∈ Metric.ball x₀ ρ,
        ((C₀*lam) • (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) -
          OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x)).PosSemidef) →
      (∀ x ∈ Metric.ball x₀ ρ, OAI.LinearAlgebra.Moore.QuaternionRankLE r (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x)) →
      (∀ x ∈ Metric.ball x₀ ρ, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + u y) x)).PosDef) →
      (∀ x ∈ Metric.ball x₀ ρ, OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots
        (fun y => B y + u y) x) = lam^r * μ x) →
      (∀ x ∈ Metric.ball x₀ ρ, m₀ ≤ μ x) →
      (∀ x, ‖x-x₀‖ = ρ → u x ≤ 0) →
      c*ρ^2*m₀^(1+1/((m-r:ℕ):ℝ)) ≤ (-u x₀)*μ x₀ := by
  obtain ⟨c,hc,hbound⟩ := rank_concentration_of_scalar_shift_bound m r hr hC.le
  refine ⟨c,hc,?_⟩
  intro x₀ ρ lam m₀ hρ hlam hm₀ hml B u μ hB hu hBc huc hBpos hBupper hBrank hpos hPDE hμ hbd
  apply hbound x₀ ρ lam m₀ hρ hlam hm₀ hml B u μ hB hu hBc huc hpos
    _ hPDE hμ hbd
  intro x hx a ha
  exact OAI.LinearAlgebra.Moore.mooreDet_add_scalar_le_of_rank (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots B x)
    (hBpos x hx) (hBupper x hx) (hBrank x hx) hr.le (mul_nonneg hC.le hlam.le) ha

end OAI.Analysis.PDE.Concentration
