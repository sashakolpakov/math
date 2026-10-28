import OAI.Analysis.PDE.Elliptic.Boundary.InteriorDepth
import OAI.Analysis.PDE.Elliptic.Boundary.RemainderOscillation

/-! Interior scaled Hölder control of the actual physical Hessian, written
in boundary coordinates, with constants uniform down to the boundary. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem log_equation_chart_physical_interior_oscillation {n : ℕ}
    {r B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → ℝ}
    {G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4}
    (hr : ContDiff ℝ 1 r) (_ : ContDiff ℝ 3 B) (hG : ContDiff ℝ 3 G)
    {ν : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4} (hν : ‖ν‖ = 1)
    {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) 4)} (hU : IsOpen U)
    (hGU : ∀ x ∈ closedHalfBall ν, G x ∈ U)
    {c lam L L₁ L₂ V : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hL : lam ≤ L)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hV : 0 < V)
    (hrG : ∀ x ∈ closedHalfBall ν, r (G x) = -c * inner ℝ ν x)
    (hG1 : ∀ x ∈ closedHalfBall ν, ‖fderiv ℝ G x‖ ≤ V)
    (_ : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 2 G x‖ ≤ V)
    (_ : ∀ x ∈ closedHalfBall ν, ‖iteratedFDeriv ℝ 3 G x‖ ≤ V) :
    ∃ σ β D : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < β ∧ β < 1 ∧ 0 < D ∧
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
      ∀ x, ‖x‖ ≤ 1 / 4 → 0 < inner ℝ ν x →
      ∀ y ∈ closedBall x (σ * inner ℝ ν x / 2),
        ‖fderiv ℝ (gradient ψ) (G y) -
          fderiv ℝ (gradient ψ) (G x)‖ ≤
            D * (‖y - x‖ / inner ℝ ν x) ^ β := by
  have hS : IsCompact (closedHalfBall ν) := by
    have he : closedHalfBall ν = closedBall 0 1 ∩ {x | 0 ≤ inner ℝ ν x} := by
      ext x; simp [closedHalfBall, mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall 0 1).inter_right
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
  obtain ⟨κ, β, C, hκ, hκ1, hβ, hβ1, hC, hdepth⟩ :=
    log_equation_hessian_at_depth hr (hS.image hG.continuous) hU
      (by rintro _ ⟨x, hx, rfl⟩; exact hGU x hx) hc hlam hL hL₁ hL₂ hV.le
  let σ := min 1 (κ / (V + 1))
  have hσ : 0 < σ := lt_min zero_lt_one (div_pos hκ (by linarith))
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hVσ : V * σ ≤ κ := by
    have ht := (le_div_iff₀ (show 0 < V + 1 by linarith)).mp (min_le_right 1 (κ / (V + 1)))
    change σ * (V + 1) ≤ κ at ht
    nlinarith
  let C' := C * (V / κ) ^ β
  let D := C'
  have hC' : 0 < C' := mul_pos hC (Real.rpow_pos_of_pos (div_pos hV hκ) _)
  have hD : 0 < D := hC'
  refine ⟨σ, β, D, hσ, hσ1, hβ, hβ1, hD, ?_⟩
  intro ψ F hψ hpos heq hell hnorm hlog hlog₂ hψ1 hψ2 x hx hxν y hy
  let h := inner ℝ ν x
  have hh : 0 < h := hxν
  have hhx : h ≤ ‖x‖ := by
    exact (le_abs_self _).trans ((abs_real_inner_le_norm ν x).trans_eq (by rw [hν, one_mul]))
  have hh1 : h ≤ 1 := by linarith
  have hxc : x ∈ closedHalfBall ν := ⟨by linarith, hxν.le⟩
  have hdist : ‖y - x‖ ≤ σ * h / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hdist_half : ‖y - x‖ ≤ h / 2 := hdist.trans
    (div_le_div_of_nonneg_right (mul_le_of_le_one_left hh.le hσ1) (by norm_num))
  have hyc : y ∈ closedHalfBall ν := by
    constructor
    · have hn := norm_add_le (y - x) x
      rw [sub_add_cancel] at hn
      linarith
    · have hi := abs_real_inner_le_norm ν (y - x)
      rw [hν, one_mul, inner_sub_right] at hi
      have hl := (abs_le.mp hi).1
      change -‖y - x‖ ≤ inner ℝ ν y - h at hl
      linarith
  have hGdiff : ‖G y - G x‖ ≤ V * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ closedHalfBall ν) => hG.differentiable (by norm_num) z)
      hG1 (convex_closedHalfBall ν) hxc hyc
  have hGball : G y ∈ closedBall (G x) (κ * h) := by
    rw [mem_closedBall, _root_.dist_eq_norm]
    have ht := mul_le_mul_of_nonneg_left hdist hV.le
    have ht' := mul_le_mul_of_nonneg_right hVσ hh.le
    nlinarith
  have hb := (hdepth ψ F hψ hpos heq hell hnorm hlog hlog₂ (G x)
    ⟨x, hxc, rfl⟩ h hh hh1 (hrG x hxc) (G y) hGball).2
  have hfrac : dist (G y) (G x) / (κ * h) ≤ (V / κ) * (‖y - x‖ / h) := by
    rw [_root_.dist_eq_norm]
    calc
      ‖G y - G x‖ / (κ * h) ≤ (V * ‖y - x‖) / (κ * h) :=
        div_le_div_of_nonneg_right hGdiff (mul_pos hκ hh).le
      _ = (V / κ) * (‖y - x‖ / h) := by field_simp
  have hpow := Real.rpow_le_rpow (show 0 ≤ dist (G y) (G x) / (κ * h) by positivity) hfrac hβ.le
  rw [Real.mul_rpow (div_pos hV hκ).le (div_nonneg (norm_nonneg _) hh.le)] at hpow
  have hphys : ‖fderiv ℝ (gradient ψ) (G y) - fderiv ℝ (gradient ψ) (G x)‖ ≤
      C' * (‖y - x‖ / h) ^ β := by
    rw [norm_fderiv_gradient_sub (hψ.of_le (by norm_num))]
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC.le).trans_eq (by dsimp [C']; ring))
  exact hphys

end OAI.Analysis.PDE.Elliptic
