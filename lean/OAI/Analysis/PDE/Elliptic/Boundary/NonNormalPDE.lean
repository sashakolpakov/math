import OAI.Analysis.PDE.Elliptic.Boundary.TangentExpansion
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Interior
import OAI.Analysis.PDE.Elliptic.Boundary.FlatApproach

/-! Actual nonlinear PDE estimates imply quantitative approach to the
boundary for every non-normal Hessian component in flattened coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

theorem log_equation_nonnormal_boundary_approach {n : ℕ}
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
    (hG1 : ∀ x ∈ closedHalfBall ν, ‖fderiv ℝ G x‖ ≤ V)
    (hG2 : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 2 G x‖ ≤ V)
    (hG3 : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 3 G x‖ ≤ V) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧
      ∀ (ψ F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ), ContDiff ℝ 4 ψ →
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
      (∀ x ∈ closedHalfBall ν, ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))‖ ≤ V) →
      (∀ x ∈ closedHalfBall ν, ‖pullbackEllipticOperator (fderiv ℝ P (G x))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)))‖ ≤ V) →
      (∀ x ∈ closedHalfBall ν, ∀ w, lamp * ‖w‖ ^ 2 ≤ inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G x))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))) w)) →
      (∀ x ∈ closedHalfBall ν, ∀ w, inner ℝ w
        (pullbackEllipticOperator (fderiv ℝ P (G x))
          (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))) w) ≤ Lp * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall ν, DifferentiableAt ℝ F (G x)) →
      (∀ x ∈ openHalfBall ν, ‖fderiv ℝ F (G x)‖ / |F (G x)| ≤ V) →
      (∀ x, ‖x‖ ≤ 2 → inner ℝ ν x = 0 → ψ (G x) = B (G x)) →
      ∀ z, ‖z‖ ≤ 1 / 8 → inner ℝ ν z = 0 →
      ∀ h : ℝ, 0 < h → h ≤ 1 / 8 →
      let H := fderiv ℝ (gradient (fun y => ψ (G y) - B (G y))) (z + h • ν) -
        fderiv ℝ (gradient (fun y => ψ (G y) - B (G y))) z
      ‖H - inner ℝ (H ν) ν • rankOne ℝ ν ν‖ ≤ M * h ^ γ := by
  obtain ⟨a, ha, ha1, hexp⟩ := log_equation_chart_tangent_expansion (n := n + 1) hlamp hLp
  obtain ⟨A, hA, hexp⟩ := hexp P G B hP hG hB V hV.le
  obtain ⟨σ, b, D, hσ, hσ1, hb, hb1, hD, hint⟩ :=
    log_equation_chart_interior_oscillation hr hB hG hν hU hGU hc hlam hL hL₁ hL₂ hV hrG hG1 hG2 hG3
  let γ := a * b / (1 + b)
  have hγ : 0 < γ := div_pos (mul_pos ha hb) (by linarith)
  have hγ1 : γ < 1 := by
    apply (div_lt_iff₀ (by linarith : 0 < 1 + b)).2
    have hm := mul_lt_mul_of_pos_right ha1 hb
    nlinarith
  let A' := A * (4 : ℝ) ^ a
  let M := 8 * (8 * A' / σ ^ (1 + a) + D)
  have hA' : 0 < A' := mul_pos hA (Real.rpow_pos_of_pos (by norm_num) _)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨γ, M, hγ, hγ1, hM, ?_⟩
  intro ψ F hψ hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 hAop hAA hloP hhiP hF hF1 hzero z hz hzν h hh hh8
  have hψ3 : ContDiff ℝ 3 ψ := hψ.of_le (by norm_num)
  have heqg (x) (hx : x ∈ openHalfBall ν) :
      (fun y => OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) =ᶠ[𝓝 (G x)] F := by
    have hxc : x ∈ closedHalfBall ν := ⟨hx.1.le, hx.2.le⟩
    have hrx : r (G x) < 0 := by rw [hrG x hxc]; nlinarith [mul_pos hc hx.2]
    have hopen : IsOpen (U ∩ {y | r y < 0}) := hU.inter (isOpen_lt hr.continuous continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hGU x hxc, hrx⟩] with y hy
    exact heq y hy
  have hex := hexp ν hν hinv ψ F hψ3 hψ1 hψ2 hAop hAA hloP hhiP hF hF1 heqg hzero
  have hi := hint ψ F hψ hpos heq hell hnorm hlog hlog₂ hψ1 hψ2
  have hw : ContDiff ℝ 3 (fun y => ψ (G y) - B (G y)) := (hψ3.comp hG).sub (hB.comp hG)
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
  have hrem := flat_hessian_approach_remainder hw hν (by linarith) hzν
    (fun y hy hyv => sub_eq_zero.mpr (hzero y (by linarith) hyv))
    hh (by linarith) hσ hσ1 hA'.le hD.le ha hb
    (fun e he hνe y hy hyν => by
      have he' := hex e he hνe z (by linarith) hzν (4 * h) (by positivity) (by linarith) y
        (by linarith) hyν
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hh.le] at he'
      exact he'.trans_eq (by dsimp [A']; ring))
    (fun y hy => by
      have hy' : y ∈ closedBall x (σ * inner ℝ ν x / 2) := by simpa only [hheight] using hy
      simpa only [hheight] using hi x hxnorm (by rwa [hheight]) y hy')
  dsimp only
  convert hrem using 1 ; dsimp [γ, M] ; ring

end OAI.Analysis.PDE.Elliptic
