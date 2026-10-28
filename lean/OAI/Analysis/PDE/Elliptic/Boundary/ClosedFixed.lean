import OAI.Analysis.PDE.Elliptic.Boundary.ClosedChart
import OAI.Analysis.PDE.Elliptic.Boundary.FixedChart

/-! Full closed-chart Hölder control using only physical operator bounds;
the transformed ellipticity constants are derived from inverse Jacobians. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem log_equation_closed_fixed_chart_holder {n : ℕ}
    {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ}
    {P G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4}
    (hr : ContDiff ℝ 1 r) (hB : ContDiff ℝ 3 B) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    {ν : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4} (hν : ‖ν‖ = 1)
    {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)} (hU : IsOpen U)
    (hGU : ∀ x ∈ closedHalfBall ν, G x ∈ U)
    {c lam L L₁ L₂ V C0 : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hL : lam ≤ L)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hV : 0 < V) (hC0 : 0 < C0)
    (hrG : ∀ x ∈ closedHalfBall ν, r (G x) = -c * inner ℝ ν x)
    (hinv : ∀ x ∈ closedHalfBall ν, (fun y => P (G y)) =ᶠ[𝓝 x] id)
    (hP1 : ∀ x ∈ closedHalfBall ν, ‖fderiv ℝ P (G x)‖ ≤ C0)
    (hG1 : ∀ x ∈ closedHalfBall ν, ‖fderiv ℝ G x‖ ≤ C0)
    (hG2 : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 2 G x‖ ≤ C0)
    (hG3 : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 3 G x‖ ≤ C0) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧
      ∀ (ψ F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ), ContDiff ℝ 4 ψ → Continuous F →
      (∀ x ∈ U ∩ {y | r y < 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ U ∩ {y | r y < 0}, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ U ∩ {y | r y < 0}, ∀ v,
        lam * ‖v‖ ^ 2 ≤ OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ U ∩ {y | r y < 0}, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ V) →
      (∀ x ∈ U ∩ {y | r y < 0}, ∀ y ∈ U ∩ {y | r y < 0},
        |Real.log (F x) - Real.log (F y)| ≤ L₁ * dist x y) →
      (∀ x ∈ U ∩ {y | r y < 0}, ∀ v,
        -L₂ * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0) →
      (∀ x ∈ closedHalfBall ν, ‖fderiv ℝ ψ (G x)‖ ≤ V) →
      (∀ x ∈ closedHalfBall ν, ‖fderiv ℝ (gradient ψ) (G x)‖ ≤ V) →
      (∀ x ∈ closedHalfBall ν, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef) →
      (∀ x ∈ closedHalfBall ν, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) w)) →
      (∀ x ∈ closedHalfBall ν, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))‖ ≤ V) →
      (∀ x ∈ closedHalfBall ν, DifferentiableAt ℝ F (G x)) →
      (∀ x ∈ closedHalfBall ν, F (G x) ≠ 0) →
      (∀ x ∈ closedHalfBall ν, ‖fderiv ℝ F (G x)‖ / |F (G x)| ≤ V) →
      (∀ x, ‖x‖ ≤ 2 → inner ℝ ν x = 0 → ψ (G x) = B (G x)) →
      ∀ x y, ‖x‖ ≤ 1 / 8 → ‖y‖ ≤ 1 / 8 → 0 ≤ inner ℝ ν x →
        0 ≤ inner ℝ ν y →
        ‖fderiv ℝ (gradient ψ) (G x) - fderiv ℝ (gradient ψ) (G y)‖ ≤
          M * ‖x - y‖ ^ γ := by
  let W := V + C0 + C0 ^ 2 * V + 1
  have hW : 0 < W := by dsimp [W]; positivity
  have hCV : 0 ≤ C0 ^ 2 * V := mul_nonneg (sq_nonneg C0) hV.le
  have hVW : V ≤ W := by dsimp [W]; linarith
  have hCW : C0 ≤ W := by dsimp [W]; linarith
  have hC2W : C0 ^ 2 * V ≤ W := by dsimp [W]; linarith
  obtain ⟨γ, D, hγ, hγ1, hD, hholder⟩ := log_equation_closed_chart_holder
    hr hB hG hP hν hU hGU hc hlam hL hL₁ hL₂ hW
    (div_pos hlam (sq_pos_of_pos hC0)) (mul_pos hV (sq_pos_of_pos hC0))
    hrG hinv (fun x hx => (hP1 x hx).trans hCW)
    (fun x hx => (hG1 x hx).trans hCW)
    (fun x hx => (hG2 x hx).trans hCW)
    (fun x hx => (hG3 x hx).trans hCW)
  refine ⟨γ, D, hγ, hγ1, hD, ?_⟩
  intro ψ F hψ hFc hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 hposS hloS hAop hF hFne hF1 hzero
  have hupper (z) (hz : z ∈ closedHalfBall ν) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) :
      inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G z)) w) ≤ V * ‖w‖ ^ 2 := by
    apply (real_inner_le_norm _ _).trans
    have hh := (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G z))).le_opNorm w
    have hh' := hh.trans (mul_le_mul_of_nonneg_right (hAop z hz) (norm_nonneg w))
    nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg w)]
  have hb (z) (hz : z ∈ closedHalfBall ν) := pullbackEllipticOperator_bounds_of_inverse
    (fderiv ℝ P (G z)) (fderiv ℝ G z) (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G z)))
    hC0 hlam.le hV.le
    (chart_jacobians_inverse (hP.differentiable (by norm_num) (G z))
      (hG.differentiable (by norm_num) z) (hinv z hz)).1
    (hP1 z hz) (hG1 z hz) (hloS z hz) (hupper z hz)
  have hAA (z) (hz : z ∈ closedHalfBall ν) :
      ‖pullbackEllipticOperator (fderiv ℝ P (G z))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G z)))‖ ≤ W := by
    apply (pullbackEllipticOperator_norm_bound _ _).trans
    apply le_trans _ hC2W
    exact mul_le_mul (by nlinarith [norm_nonneg (fderiv ℝ P (G z)), hP1 z hz])
      (hAop z hz) (norm_nonneg _) (sq_nonneg C0)
  exact hholder ψ F hψ hFc hpos heq hell
    (fun x hx => (hnorm x hx).trans hVW) hlog hlog₂
    (fun x hx => (hψ1 x hx).trans hVW) (fun x hx => (hψ2 x hx).trans hVW) hposS hloS
    (fun x hx => (hAop x hx).trans hVW) hAA (fun x hx w => (hb x hx w).1)
    (fun x hx w => (hb x hx w).2) hF hFne (fun x hx => (hF1 x hx).trans hVW) hzero

end OAI.Analysis.PDE.Elliptic
