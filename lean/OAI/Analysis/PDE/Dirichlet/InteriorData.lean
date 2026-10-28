import OAI.Analysis.PDE.Dirichlet.InteriorHolder
import OAI.Analysis.PDE.Dirichlet.LogLipschitz
import OAI.Analysis.PDE.Elliptic.HessianNorm

open Set Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- Positive C² prescribed density gives the data bounds required by the
interior estimate. The conclusion controls the actual second Fréchet derivative,
uniformly for all solutions with the stated C² and ellipticity bounds. -/
theorem log_equation_interior_holder_of_density {n : ℕ} {lam L V : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) (hV : 0 ≤ V)
    (F : CoordinateSpace (n + 1) 4 → ℝ) (hF : ContDiff ℝ 2 F)
    (z : CoordinateSpace (n + 1) 4) (hFpos : ∀ x ∈ closedBall z 1, 0 < F x) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ ψ : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 ψ →
      (∀ x ∈ closedBall z 1, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ closedBall z 1, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ closedBall z 1, ∀ v,
        lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ closedBall z 1, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ V) →
      ∀ r, 0 < r → r ≤ 1 → ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
        ‖fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B * r ^ α := by
  obtain ⟨L₁, hL₁, hlog⟩ := exists_log_lipschitz_bound hF
    (isCompact_closedBall z 1) (convex_closedBall z 1) hFpos
  obtain ⟨L₂, hL₂, hlog₂⟩ := exists_log_second_directional_bound hF
    (isCompact_closedBall z 1) hFpos
  obtain ⟨α, B, hα, hα1, hB, hmain⟩ := log_equation_interior_holder
    (n := n) hlam hL hL₁.le hL₂.le hV
  refine ⟨α, B, hα, hα1, hB, ?_⟩
  intro ψ hψ hpos heq hell hnorm r hr hr1 x hx y hy
  have hψ₂ : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have h := hmain ψ F z hψ hpos heq hell (fun x hx ↦ by
    rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient hψ₂]
    exact hnorm x hx) hlog (fun x hx ↦ hlog₂ x (ball_subset_closedBall hx)) r hr hr1 x hx y hy
  rwa [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub hψ₂] at h

end OAI.Analysis.PDE.Dirichlet
