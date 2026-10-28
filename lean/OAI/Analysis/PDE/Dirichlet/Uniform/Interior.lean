import OAI.Analysis.PDE.Dirichlet.InteriorHolder
import OAI.Analysis.PDE.Dirichlet.RescalePotential
import OAI.Analysis.PDE.Elliptic.HessianNorm

open Set Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- The rescaled interior constants are uniform in the center and in every
solution and density satisfying the displayed quantitative data bounds. -/
theorem log_equation_uniform_interior_ball {n : ℕ} {lam L L₁ L₂ V R : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hV : 0 ≤ V) (hR : 0 < R) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ (ψ F : CoordinateSpace (n + 1) 4 → ℝ) (z : CoordinateSpace (n + 1) 4),
      ContDiff ℝ 4 ψ →
      (∀ x ∈ closedBall z R, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ closedBall z R, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ closedBall z R, ∀ v,
        lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ closedBall z R, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ V) →
      (∀ x ∈ closedBall z R, ∀ y ∈ closedBall z R,
        |Real.log (F x) - Real.log (F y)| ≤ L₁ * dist x y) →
      (∀ x ∈ ball z R, ∀ v,
        -L₂ * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0) →
      ∀ r, 0 < r → r ≤ R → ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
        ‖fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B * r ^ α := by
  let E := CoordinateSpace (n + 1) 4
  obtain ⟨α, C, hα, hα1, hC, hc⟩ := log_equation_interior_holder (n := n)
    hlam hL (mul_nonneg hR.le hL₁) (mul_nonneg (sq_nonneg R) hL₂) hV
  refine ⟨α, C / R ^ α, hα, hα1, div_pos hC (Real.rpow_pos_of_pos hR α), ?_⟩
  intro ψ F z hψ hpos heq hell hnorm hlog hlog₂
  let ψ₀ := rescalePotential ψ z R
  let F₀ : E → ℝ := fun x ↦ F (OAI.Analysis.PDE.Elliptic.rescalePoint z R x)
  have hψ₂ : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hψ₀ : ContDiff ℝ 4 ψ₀ := contDiff_rescalePotential hψ z R
  have himage (x : E) (hx : x ∈ closedBall (0 : E) 1) :
      OAI.Analysis.PDE.Elliptic.rescalePoint z R x ∈ closedBall z R := by
    rw [mem_closedBall, OAI.Analysis.PDE.Elliptic.dist_rescalePoint z x hR.le]
    have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    nlinarith
  have himage' (x : E) (hx : x ∈ ball (0 : E) 1) :
      OAI.Analysis.PDE.Elliptic.rescalePoint z R x ∈ ball z R := by
    rw [mem_ball, OAI.Analysis.PDE.Elliptic.dist_rescalePoint z x hR.le]
    have hx' : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    nlinarith
  have hquat (x : E) : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ₀ x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) :=
    quaternionHessian_rescalePotential OAI.Analysis.Calculus.Quaternion.fourSlots hψ₂ z hR.ne' x
  have hsecond (x : E) : fderiv ℝ (fderiv ℝ ψ₀) x =
      fderiv ℝ (fderiv ℝ ψ) (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) :=
    second_fderiv_rescalePotential hψ₂ z hR.ne' x
  have hdist (x y : E) : dist (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) (OAI.Analysis.PDE.Elliptic.rescalePoint z R y) =
      R * dist x y := by
    rw [show dist x y = ‖x - y‖ from _root_.dist_eq_norm x y]
    simp only [_root_.dist_eq_norm, OAI.Analysis.PDE.Elliptic.rescalePoint, add_sub_add_left_eq_sub,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hline (x v : E) (t : ℝ) : OAI.Analysis.PDE.Elliptic.rescalePoint z R (x + t • v) =
      OAI.Analysis.PDE.Elliptic.rescalePoint z R x + t • (R • v) := by
    simp only [OAI.Analysis.PDE.Elliptic.rescalePoint, smul_add, smul_smul, mul_comm R t, add_assoc]
  have hbase := hc ψ₀ F₀ (0 : E) hψ₀
    (fun x hx ↦ by rw [hquat]; exact hpos _ (himage x hx))
    (fun x hx ↦ by rw [hquat]; exact heq _ (himage x hx))
    (fun x hx v ↦ by rw [hquat]; exact hell _ (himage x hx) v)
    (fun x hx ↦ by
      rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient (hψ₀.of_le (by norm_num)), hsecond]
      exact hnorm _ (himage x hx))
    (fun x hx y hy ↦ by
      have h := hlog _ (himage x hx) _ (himage y hy)
      rw [hdist] at h
      exact h.trans_eq (by ring))
    (fun x hx v ↦ by
      have h := hlog₂ _ (himage' x hx) (R • v)
      have he : (fun t : ℝ ↦ Real.log (F₀ (x + t • v))) =
          (fun t : ℝ ↦ Real.log (F (OAI.Analysis.PDE.Elliptic.rescalePoint z R x + t • (R • v)))) := by
        funext t
        change Real.log (F (OAI.Analysis.PDE.Elliptic.rescalePoint z R (x + t • v))) = _
        rw [hline]
      rw [he]
      convert h using 1 ; simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR] ; ring)
  intro r hr hrR x hx y hy
  have hinverse (a : E) (ha : a ∈ closedBall z r) :
      R⁻¹ • (a - z) ∈ closedBall (0 : E) (r / R) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    have ha' : ‖a - z‖ ≤ r := by
      have hd : dist a z = ‖a - z‖ := _root_.dist_eq_norm a z
      exact hd ▸ mem_closedBall.mp ha
    calc
      R⁻¹ * ‖a - z‖ = ‖a - z‖ / R := by ring
      _ ≤ r / R := div_le_div_of_nonneg_right ha' hR.le
  have h := hbase (r / R) (div_pos hr hR) ((div_le_one hR).mpr hrR)
    _ (hinverse x hx) _ (hinverse y hy)
  rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub (hψ₀.of_le (by norm_num)), hsecond, hsecond,
    OAI.Analysis.PDE.Elliptic.rescalePoint_inverse z x hR.ne', OAI.Analysis.PDE.Elliptic.rescalePoint_inverse z y hR.ne',
    Real.div_rpow hr.le hR.le] at h
  exact h.trans_eq (by ring)

end OAI.Analysis.PDE.Dirichlet
