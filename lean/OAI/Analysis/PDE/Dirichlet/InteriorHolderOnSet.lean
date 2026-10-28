import OAI.Analysis.PDE.Dirichlet.Uniform.Interior
import Mathlib.Analysis.Calculus.MeanValue

open Set Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- Uniform centered oscillation gives a genuine pairwise Hölder estimate,
including pairs farther apart than the local radius. -/
theorem holder_of_uniform_centered_oscillation
    {E Y : Type*} [MetricSpace E] [NormedAddCommGroup Y]
    {u : E → Y} {K : Set E} {R α C V : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hC : 0 < C) (hV : 0 ≤ V)
    (hbound : ∀ x ∈ K, ‖u x‖ ≤ V)
    (hosc : ∀ z ∈ K, ∀ r, 0 < r → r ≤ R →
      ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r, ‖u x - u y‖ ≤ C * r ^ α) :
    ∀ x ∈ K, ∀ y ∈ K,
      ‖u x - u y‖ ≤ (C + 2 * V / R ^ α) * (dist x y) ^ α := by
  intro x hx y hy
  have hpow : 0 < R ^ α := Real.rpow_pos_of_pos hR α
  have hcoef : 0 ≤ 2 * V / R ^ α := div_nonneg (by positivity) hpow.le
  by_cases hzero : dist x y = 0
  · have hxy := dist_eq_zero.mp hzero
    subst y
    simp [Real.zero_rpow hα.ne']
  have hd : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
  by_cases hnear : dist x y ≤ R
  · have h := hosc x hx (dist x y) hd hnear x (by simp [hd.le]) y
      (by simp [mem_closedBall, dist_comm])
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le α))
  · have hlarge : R ^ α ≤ (dist x y) ^ α :=
      Real.rpow_le_rpow hR.le (le_of_not_ge hnear) hα.le
    calc
      ‖u x - u y‖ ≤ ‖u x‖ + ‖u y‖ := norm_sub_le _ _
      _ ≤ 2 * V := by linarith [hbound x hx, hbound y hy]
      _ = (2 * V / R ^ α) * R ^ α := by field_simp
      _ ≤ (2 * V / R ^ α) * (dist x y) ^ α := mul_le_mul_of_nonneg_left hlarge hcoef
      _ ≤ (C + 2 * V / R ^ α) * (dist x y) ^ α :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le α)

/-- Interior C²,α estimate on any region with a uniform interior-ball radius.
All constants precede the domain, the solution, and the prescribed density. -/
theorem log_equation_holder_on_interior_set {n : ℕ} {lam L L₁ L₂ V R : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hV : 0 ≤ V) (hR : 0 < R) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ (Ω K : Set (CoordinateSpace (n + 1) 4))
        (ψ F : CoordinateSpace (n + 1) 4 → ℝ),
      (∀ z ∈ K, closedBall z R ⊆ Ω) → ContDiff ℝ 4 ψ →
      (∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ Ω, ∀ v,
        lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Ω, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ V) →
      (∀ x ∈ Ω, DifferentiableAt ℝ (fun z ↦ Real.log (F z)) x) →
      (∀ x ∈ Ω, ‖fderiv ℝ (fun z ↦ Real.log (F z)) x‖ ≤ L₁) →
      (∀ x ∈ Ω, ∀ v,
        -L₂ * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0) →
      ∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B * (dist x y) ^ α := by
  obtain ⟨α, C, hα, hα1, hC, hc⟩ :=
    log_equation_uniform_interior_ball (n := n) hlam hL hL₁ hL₂ hV hR
  refine ⟨α, C + 2 * V / R ^ α, hα, hα1, by positivity, ?_⟩
  intro Ω K ψ F hballs hψ hpos heq hell hnorm hdiff hlog hlog₂
  have hKΩ : K ⊆ Ω := fun x hx ↦ hballs x hx (by simp [hR.le])
  apply holder_of_uniform_centered_oscillation (u := fderiv ℝ (fderiv ℝ ψ)) hR hα hC hV
    (fun x hx ↦ hnorm x (hKΩ hx))
  intro z hz
  apply hc ψ F z hψ
    (fun x hx ↦ hpos x (hballs z hz hx))
    (fun x hx ↦ heq x (hballs z hz hx))
    (fun x hx v ↦ hell x (hballs z hz hx) v)
    (fun x hx ↦ hnorm x (hballs z hz hx))
  · intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x hx ↦ hdiff x (hballs z hz hx))
      (fun x hx ↦ hlog x (hballs z hz hx)) (convex_closedBall z R) hy hx
    simpa only [Real.norm_eq_abs, _root_.dist_eq_norm] using h
  · intro x hx v
    exact hlog₂ x (hballs z hz (ball_subset_closedBall hx)) v

end OAI.Analysis.PDE.Dirichlet
