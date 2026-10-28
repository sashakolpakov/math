import OAI.Analysis.PDE.Elliptic.Boundary.InteriorBall
import OAI.Analysis.PDE.Elliptic.Boundary.InteriorScale

/-! Actual interior Hessian oscillation at a fixed fraction of the boundary
depth. Both the interior ball and its Evans--Krylov bound are derived. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

local instance {n : ℕ} : NormedAddCommGroup
    (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 →L[ℝ] ℝ) := inferInstance

theorem log_equation_hessian_at_depth {n : ℕ}
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 1 r)
    {K U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {c : ℝ} (hc : 0 < c)
    {lam L L₁ L₂ V : ℝ} (hlam : 0 < lam) (hL : lam ≤ L)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hV : 0 ≤ V) :
    ∃ κ β C : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 0 < β ∧ β < 1 ∧ 0 < C ∧
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
      ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ 1 → r x = -c * h →
      ∀ y ∈ closedBall x (κ * h), y ∈ U ∩ {y | r y < 0} ∧
        ‖fderiv ℝ (fderiv ℝ ψ) y - fderiv ℝ (fderiv ℝ ψ) x‖ ≤
          C * (dist y x / (κ * h)) ^ β := by
  obtain ⟨κ, hκ, hκ1, hball⟩ := exists_uniform_sublevel_balls hr hK hU hKU hc
  obtain ⟨β, C, hβ, hβ1, hC, hholder⟩ :=
    log_equation_uniform_interior_scale hlam hL hL₁ hL₂ hV
  refine ⟨κ, β, C, hκ, hκ1, hβ, hβ1, hC, ?_⟩
  intro ψ F hψ hpos heq hell hnorm hlog hlog₂ x hx h hh hh1 hrx y hy
  have hkh : 0 < κ * h := mul_pos hκ hh
  have hkh1 : κ * h ≤ 1 := (mul_le_of_le_one_left hh.le hκ1).trans hh1
  have hsubset := hball x hx h hh hh1 hrx
  refine ⟨hsubset hy, ?_⟩
  have hb := hholder (κ * h) hkh hkh1 ψ F x hψ
    (fun z hz => hpos z (hsubset hz)) (fun z hz => heq z (hsubset hz))
    (fun z hz => hell z (hsubset hz)) (fun z hz => hnorm z (hsubset hz))
    (fun z hz w hw => hlog z (hsubset hz) w (hsubset hw))
    (fun z hz => hlog₂ z (hsubset (ball_subset_closedBall hz)))
  by_cases hxy : y = x
  · subst y
    simp [hβ.ne']
  · have hd : 0 < dist y x := dist_pos.mpr hxy
    exact hb (dist y x) hd (mem_closedBall.mp hy) y (by simp only [mem_closedBall, le_refl])
      x (mem_closedBall_self hd.le)

end OAI.Analysis.PDE.Elliptic
