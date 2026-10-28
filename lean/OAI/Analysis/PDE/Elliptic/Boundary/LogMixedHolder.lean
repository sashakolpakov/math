import OAI.Analysis.PDE.Elliptic.Boundary.MixedHolder

/-! Actual differentiated log determinant equation implies boundary mixed-Hessian Hölder control. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology

theorem log_equation_boundary_mixed_holder {n : ℕ} [Nonempty (Fin n)]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ V : ℝ, 0 ≤ V →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), ‖v‖ = 1 →
      ∀ (P F T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
        (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ),
      ContDiff ℝ 3 u → ContDiff ℝ 2 T →
      (∀ z ∈ closedHalfBall v, ContDiffAt ℝ 2 F z) →
      (∀ z ∈ closedHalfBall v, DifferentiableAt ℝ P (F z)) →
      (∀ z ∈ closedHalfBall v, (fun y => P (F y)) =ᶠ[𝓝 z] id) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖fderiv ℝ F z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 F z‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ‖pullbackEllipticOperator (fderiv ℝ P (F z))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z)))‖ ≤ V) →
      (∀ z ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (F z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))) w)) →
      (∀ z ∈ closedHalfBall v, ∀ w, inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (F z))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (F z))) w) ≤ L * ‖w‖ ^ 2) →
      (∀ z ∈ openHalfBall v, DifferentiableAt ℝ f (F z)) →
      (∀ z ∈ openHalfBall v, ‖fderiv ℝ f (F z)‖ / |f (F z)| ≤ V) →
      (∀ z ∈ openHalfBall v,
        (fun y => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) =ᶠ[𝓝 (F z)] f) →
      (∀ z, ‖z‖ ≤ 1 → inner ℝ v z = 0 → fieldDerivative u T (F z) = 0) →
      ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
        |chartMixedHessian u T F v z - chartMixedHessian u T F v z'| ≤ C * ‖z - z'‖ ^ α := by
  obtain ⟨α, hα, hα1, hholder⟩ := log_equation_boundary_field_holder (n := n) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro V hV
  obtain ⟨C, hC, hholder⟩ := hholder V hV
  refine ⟨C + V ^ 3 + 2 * V ^ 4, by positivity, ?_⟩
  intro v hv P F T u f hu hT hF hP hinv hDu hD2u hT0 hT1 hT2 hF1 hF2 hA hB hlo hhi hf hf1 heq hzero
  have hn := hholder v hv P F T u f hu hT hF hP hinv hDu hD2u hT0 hT1 hT2
    hF1 hF2 hA hB hlo hhi hf hf1 heq hzero
  exact chart_mixed_holder_from_normal (hu.of_le (by norm_num)) hT hv hV hα1.le
    hF hDu hD2u hT1 hT2 hF1 hF2 hn

end OAI.Analysis.PDE.Elliptic
