import OAI.Analysis.PDE.Dirichlet.InteriorData
import OAI.Analysis.PDE.Dirichlet.RescalePotential

open Set Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- The interior estimate on an arbitrary physical ball, obtained by scaling
the actual potential by R⁻². This preserves its quaternionic Hessian and hence
the prescribed ellipticity constants exactly. -/
theorem log_equation_interior_holder_on_ball {n : ℕ} {lam L V R : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) (hV : 0 ≤ V) (hR : 0 < R)
    (F : CoordinateSpace (n + 1) 4 → ℝ) (hF : ContDiff ℝ 2 F)
    (z : CoordinateSpace (n + 1) 4) (hFpos : ∀ x ∈ closedBall z R, 0 < F x) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ ψ : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 ψ →
      (∀ x ∈ closedBall z R, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ closedBall z R, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ closedBall z R, ∀ v,
        lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ closedBall z R, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ V) →
      ∀ r, 0 < r → r ≤ R → ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
        ‖fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B * r ^ α := by
  let E := CoordinateSpace (n + 1) 4
  let F₀ : E → ℝ := fun x ↦ F (OAI.Analysis.PDE.Elliptic.rescalePoint z R x)
  have hF₀ : ContDiff ℝ 2 F₀ := hF.comp ((OAI.Analysis.PDE.Elliptic.rescalePoint_contDiff z R).of_le le_top)
  have himage (x : E) (hx : x ∈ closedBall (0 : E) 1) :
      OAI.Analysis.PDE.Elliptic.rescalePoint z R x ∈ closedBall z R := by
    rw [mem_closedBall, OAI.Analysis.PDE.Elliptic.dist_rescalePoint z x hR.le]
    have hnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    nlinarith
  obtain ⟨α, C, hα, hα1, hC, hc⟩ := log_equation_interior_holder_of_density
    hlam hL hV F₀ hF₀ (0 : E) (fun x hx ↦ hFpos _ (himage x hx))
  refine ⟨α, C / R ^ α, hα, hα1, div_pos hC (Real.rpow_pos_of_pos hR α), ?_⟩
  intro ψ hψ hpos heq hell hnorm
  let ψ₀ := rescalePotential ψ z R
  have hψ₂ : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have hψ₀ : ContDiff ℝ 4 ψ₀ := contDiff_rescalePotential hψ z R
  have hquat (x : E) : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ₀ x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) :=
    quaternionHessian_rescalePotential OAI.Analysis.Calculus.Quaternion.fourSlots hψ₂ z hR.ne' x
  have hsecond (x : E) : fderiv ℝ (fderiv ℝ ψ₀) x =
      fderiv ℝ (fderiv ℝ ψ) (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) :=
    second_fderiv_rescalePotential hψ₂ z hR.ne' x
  have hbase := hc ψ₀ hψ₀
    (fun x hx ↦ by rw [hquat]; exact hpos _ (himage x hx))
    (fun x hx ↦ by rw [hquat]; exact heq _ (himage x hx))
    (fun x hx v ↦ by rw [hquat]; exact hell _ (himage x hx) v)
    (fun x hx ↦ by rw [hsecond]; exact hnorm _ (himage x hx))
  intro r hr hrR x hx y hy
  have hratio : 0 < r / R := div_pos hr hR
  have hratio1 : r / R ≤ 1 := (div_le_one hR).mpr hrR
  have hinverse (a : E) (ha : a ∈ closedBall z r) :
      R⁻¹ • (a - z) ∈ closedBall (0 : E) (r / R) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    have hnorma : ‖a - z‖ ≤ r := by
      have hd : dist a z = ‖a - z‖ := _root_.dist_eq_norm a z
      exact hd ▸ mem_closedBall.mp ha
    calc
      R⁻¹ * ‖a - z‖ = ‖a - z‖ / R := by ring
      _ ≤ r / R := div_le_div_of_nonneg_right hnorma hR.le
  have h := hbase (r / R) hratio hratio1
    (R⁻¹ • (x - z)) (hinverse x hx) (R⁻¹ • (y - z)) (hinverse y hy)
  rw [hsecond, hsecond, OAI.Analysis.PDE.Elliptic.rescalePoint_inverse z x hR.ne', OAI.Analysis.PDE.Elliptic.rescalePoint_inverse z y hR.ne',
    Real.div_rpow hr.le hR.le] at h
  calc
    _ ≤ C * (r ^ α / R ^ α) := h
    _ = (C / R ^ α) * r ^ α := by ring

end OAI.Analysis.PDE.Dirichlet
