import OAI.Analysis.PDE.Elliptic.Boundary.NonNormalPDE
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Approach
import OAI.Analysis.PDE.Elliptic.Boundary.Density
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants

/-! Actual nonlinear PDE estimates imply quantitative approach of the full
physical Hessian to the boundary along flattened normal segments. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem log_equation_full_boundary_approach {n : ℕ}
    {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ}
    {P G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4}
    (hr : ContDiff ℝ 1 r) (hB : ContDiff ℝ 3 B) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    {ν : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4} (hν : ‖ν‖ = 1)
    {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)} (hU : IsOpen U)
    (hGU : ∀ x ∈ closedHalfBall ν, G x ∈ U)
    {c lam L L₁ L₂ V lamp Lp : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hL : lam ≤ L)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hV : 0 < V) (hlamp : 0 < lamp) (hLp : 0 < Lp)
    (hrG : ∀ x ∈ closedHalfBall ν, r (G x) = -c * inner ℝ ν x)
    (hinv : ∀ x ∈ closedHalfBall ν, (fun y => P (G y)) =ᶠ[𝓝 x] id)
    (hP1 : ∀ x ∈ closedHalfBall ν, ‖fderiv ℝ P (G x)‖ ≤ V)
    (hG1 : ∀ x ∈ closedHalfBall ν, ‖fderiv ℝ G x‖ ≤ V)
    (hG2 : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 2 G x‖ ≤ V)
    (hG3 : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 3 G x‖ ≤ V) :
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
      (∀ x ∈ closedHalfBall ν, ‖pullbackEllipticOperator (fderiv ℝ P (G x))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)))‖ ≤ V) →
      (∀ x ∈ closedHalfBall ν, ∀ w, lamp * ‖w‖ ^ 2 ≤ inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G x))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))) w)) →
      (∀ x ∈ closedHalfBall ν, ∀ w, inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G x))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))) w) ≤ Lp * ‖w‖ ^ 2) →
      (∀ x ∈ closedHalfBall ν, DifferentiableAt ℝ F (G x)) →
      (∀ x ∈ closedHalfBall ν, F (G x) ≠ 0) →
      (∀ x ∈ closedHalfBall ν, ‖fderiv ℝ F (G x)‖ / |F (G x)| ≤ V) →
      (∀ x, ‖x‖ ≤ 2 → inner ℝ ν x = 0 → ψ (G x) = B (G x)) →
      ∀ z, ‖z‖ ≤ 1 / 8 → inner ℝ ν z = 0 →
      ∀ h : ℝ, 0 < h → h ≤ 1 / 8 →
      ‖fderiv ℝ (gradient ψ) (G (z + h • ν)) - fderiv ℝ (gradient ψ) (G z)‖ ≤ M * h ^ γ := by
  obtain ⟨γ, M, hγ, hγ1, hM, hnon⟩ := log_equation_nonnormal_boundary_approach
    hr hB hG hP hν hU hGU hc hlam hL hL₁ hL₂ hV hlamp hLp hrG hinv hG1 hG2 hG3
  have hS : IsCompact (closedHalfBall ν) := by
    have he : closedHalfBall ν = closedBall 0 1 ∩ {x | 0 ≤ inner ℝ ν x} := by
      ext x; simp [closedHalfBall, mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall 0 1).inter_right
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
  obtain ⟨K, hK, hback⟩ := exists_compact_hessian_lipschitz
    (B := fun y => B (G y)) (hB.comp hG) hS (convex_closedHalfBall ν)
  let R := 3 * V ^ 5 + V ^ 4 + V ^ 2 * (M + K)
  let C := V ^ 2 * ((V ^ 2 + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4) * V * R) /
    (lam / V ^ 2)) + R
  have hR : 0 < R := by dsimp [R]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨γ, C, hγ, hγ1, hC, ?_⟩
  intro ψ F hψ hFc hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 hposS hloS hAop hAA hloP hhiP hF hFne hF1 hzero z hz hzν h hh hh8
  have hψ2c : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hrem := hnon ψ F hψ hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 hAop hAA hloP hhiP
    (fun y hy => hF y ⟨hy.1.le, hy.2.le⟩)
    (fun y hy => hF1 y ⟨hy.1.le, hy.2.le⟩) hzero z hz hzν h hh hh8
  let x := z + h • ν
  have hheight : inner ℝ ν x = h := by
    have hvv : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
    dsimp [x]
    rw [inner_add_right, hzν, real_inner_smul_right, hvv]
    ring
  have hxnorm : ‖x‖ ≤ 1 / 4 := by
    have ht := norm_add_le z (h • ν)
    rw [norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos hh] at ht
    exact ht.trans (by linarith)
  have hxc : x ∈ closedHalfBall ν := ⟨by linarith, by rw [hheight]; exact hh.le⟩
  have hzc : z ∈ closedHalfBall ν := ⟨by linarith, hzν.ge⟩
  have hxopen : x ∈ openHalfBall ν := ⟨by linarith, by rwa [hheight]⟩
  have hdist : ‖x - z‖ = h := by
    dsimp [x]
    rw [add_sub_cancel_left, norm_smul, hν, mul_one, Real.norm_eq_abs, abs_of_pos hh]
  have hpde (y) (hy : y ∈ openHalfBall ν) :
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G y)) = F (G y) := by
    have hyc : y ∈ closedHalfBall ν := ⟨hy.1.le, hy.2.le⟩
    apply heq (G y) ⟨hGU y hyc, ?_⟩
    change r (G y) < 0
    rw [hrG y hyc]
    nlinarith [mul_pos hc hy.2]
  have heqz := moore_equation_chart_boundary hψ2c hFc hG.continuous hν (by linarith) hzν hpde
  have hlogxz : |Real.log (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G z)))| ≤ V ^ 2 * ‖x - z‖ := by
    rw [hpde x hxopen, heqz]
    have ht := log_density_chart_lipschitz (convex_closedHalfBall ν) hF
      (fun y _ => hG.differentiable (by norm_num) y) hFne hV.le hV.le hF1 hG1 hxc hzc
    convert ht using 1 ; ring
  have hinverses := chart_jacobians_inverse (hP.differentiable (by norm_num) (G x))
    (hG.differentiable (by norm_num) x) (hinv x hxc)
  have hrank : ∃ t : ℝ,
      ‖(fderiv ℝ (gradient (fun y => ψ (G y) - B (G y))) x -
        fderiv ℝ (gradient (fun y => ψ (G y) - B (G y))) z) -
          t • rankOne ℝ ν ν‖ ≤ M * h ^ γ := by
    exact ⟨_, hrem⟩
  exact chart_hessian_approach_from_remainder hψ2c (hB.of_le (by norm_num)) hG
    hν hV hlam hγ1.le hM.le hK.le (sq_nonneg V) hxc hzc hh (by linarith) hdist.le
    hψ1 hψ2 hG1 hG2 hG3 (fderiv ℝ P (G x)) (hP1 x hxc)
    hinverses.2 hinverses.1 hrank (hback x hxc z hzc) (hposS x hxc) (hposS z hzc)
    (hloS x hxc) (hloS z hzc) (hAop x hxc) (hAop z hzc) hlogxz

end OAI.Analysis.PDE.Elliptic
