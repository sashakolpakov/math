import OAI.Analysis.PDE.Elliptic.Boundary.FullApproach
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.PhysicalInterior
import OAI.Analysis.PDE.Elliptic.Boundary.LocalHolder
import OAI.Analysis.PDE.Elliptic.Boundary.FlatGluing

/-! The actual nonlinear equation yields full Hessian Hölder control on a
closed boundary chart, including arbitrary interior and boundary pairs. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem log_equation_closed_chart_holder {n : ℕ}
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
      ∀ x y, ‖x‖ ≤ 1 / 8 → ‖y‖ ≤ 1 / 8 → 0 ≤ inner ℝ ν x →
        0 ≤ inner ℝ ν y →
        ‖fderiv ℝ (gradient ψ) (G x) - fderiv ℝ (gradient ψ) (G y)‖ ≤
          M * ‖x - y‖ ^ γ := by
  obtain ⟨a, A, ha, ha1, hA, happ⟩ := log_equation_full_boundary_approach
    hr hB hG hP hν hU hGU hc hlam hL hL₁ hL₂ hV hlamp hLp hrG hinv hP1 hG1 hG2 hG3
  obtain ⟨κ, b, Cint, hκ, hκ1, hb, hb1, hCint, hint⟩ :=
    log_equation_chart_physical_interior_oscillation
      hr hB hG hν hU hGU hc hlam hL hL₁ hL₂ hV hrG hG1 hG2 hG3
  obtain ⟨d, Ctrace, hd, hd1, hCtrace, htrace⟩ :=
    log_equation_boundary_chart_holder hlamp hLp hlam hV P G B hP hG hB
  obtain ⟨γ, D, hγ, hγ1, hD, hglue⟩ :=
    exists_flat_boundary_holder_constant
      (Y := OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)
      hν ha hb hb1 hd hκ hA.le hCint.le hCtrace.le hV.le
  refine ⟨γ, D, hγ, hγ1, hD, ?_⟩
  intro ψ F hψ hFc hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 hposS hloS hAop hAA hloP hhiP hF hFne hF1 hzero
  have heqg (x) (hx : x ∈ openHalfBall ν) :
      (fun y => OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) =ᶠ[𝓝 (G x)] F := by
    have hxc : x ∈ closedHalfBall ν := ⟨hx.1.le, hx.2.le⟩
    have hrx : r (G x) < 0 := by rw [hrG x hxc]; nlinarith [mul_pos hc hx.2]
    have hopen : IsOpen (U ∩ {y | r y < 0}) := hU.inter (isOpen_lt hr.continuous continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hGU x hxc, hrx⟩] with y hy
    exact heq y hy
  exact hglue (fun x => fderiv ℝ (gradient ψ) (G x)) hψ2
    (happ ψ F hψ hFc hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 hposS hloS
      hAop hAA hloP hhiP hF hFne hF1 hzero)
    (htrace ν hν hinv hP1 hG1 hG2 hG3 ψ F (hψ.of_le (by norm_num)) hFc
      hψ1 hψ2 hposS hAop hAA hloS hloP hhiP hF hFne hF1 heqg hzero)
    (hint ψ F hψ hpos heq hell hnorm hlog hlog₂ hψ1 hψ2)

end OAI.Analysis.PDE.Elliptic
