import OAI.Analysis.PDE.Dirichlet.SublevelClosure
import OAI.Analysis.PDE.Dirichlet.Periodic.Domain
import OAI.Analysis.PDE.Dirichlet.RealOperator
import OAI.Analysis.PDE.Elliptic.CompactOperators

open Set
open scoped ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Positivity propagates to the physical boundary from the actual equation
and positive continuous right hand side. -/
theorem quaternionHessian_posDef_on_regular_sublevel {n : ℕ}
    {r ψ F : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hF : Continuous F)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x)
    (hpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) :
    ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef := by
  have hpsd := quaternionHessian_posSemidef_on_regular_sublevel hr hreg hψ
    (fun x hx ↦ hpos x (neg_of_mem_interior_regular_sublevel hreg hx))
  have hclosed := equality_on_regular_sublevel_of_interior hr hreg
    (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ) hF
    (fun x hx ↦ heq x (neg_of_mem_interior_regular_sublevel hreg hx))
  intro x hx
  apply complexify_posDef_of_posSemidef_mooreDet_pos _ (hpsd x hx)
  rw [hclosed x hx]
  exact hFpos x hx

theorem logRealOperator_norm_le_of_symbol {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Q) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (h : ∀ v : CoordinateSpace n 4,
      c * ‖v‖ ^ 2 ≤ logPrincipalSymbol A v ∧ logPrincipalSymbol A v ≤ C * ‖v‖ ^ 2) :
    ‖logRealOperator A‖ ≤ C := by
  apply OAI.Analysis.PDE.Elliptic.norm_le_of_nonneg_quadratic _ (logRealOperator_isSymmetric A) hC
  · intro v
    rw [logRealOperator_symbol]
    exact (mul_nonneg hc (sq_nonneg _)).trans (h v).1
  · intro v
    rw [logRealOperator_symbol]
    exact (h v).2

end OAI.Analysis.PDE.Dirichlet
