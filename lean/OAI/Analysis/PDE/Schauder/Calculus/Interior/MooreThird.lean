import OAI.Analysis.PDE.Schauder.Calculus.Interior.ThirdPointwise
import OAI.Analysis.PDE.Schauder.Calculus.Interior.MooreEquation

noncomputable section
open Set Metric InnerProductSpace
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance mooreThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance mooreThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance mooreThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance mooreThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance mooreThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance mooreThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance mooreOriginalFirstGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance mooreOriginalFirstSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance mooreOriginalSecondGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance mooreOriginalSecondSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

theorem stored_pullback_first_second_bound (e : E ≃ₗᵢ[ℝ] V)
    {Γ K : Set V} {hΓK : Γ ⊆ K} {α R : ℝ}
    (u : V → ℝ) (hu : ContDiff ℝ 2 u) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΓK α) (hUn : ‖U‖ ≤ R)
    (hU₁ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x)
    (hU₂ : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) :
    (∀ x ∈ e ⁻¹' K, ‖fderiv ℝ (u ∘ e) x‖ ≤ R) ∧
    (∀ x ∈ e ⁻¹' K, ‖fderiv ℝ (fderiv ℝ (u ∘ e)) x‖ ≤ R) := by
  constructor
  · intro x hx
    apply (OAI.Analysis.PDE.Dirichlet.norm_fderiv_isometry_comp_le e u (hu.differentiable (by norm_num)) x).trans
    rw [← hU₁ ⟨e x,hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U).norm_coe_le_norm _).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le U).trans hUn)
  · intro x hx
    apply (OAI.Analysis.PDE.Dirichlet.norm_second_isometry_comp_le e u hu x).trans
    rw [← hU₂ ⟨e x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le U.val.2.2 _).trans
      (((le_max_right _ _).trans (le_max_right _ _)).trans hUn)

/-- A uniform interior C³,α estimate for genuine smooth solutions of the
Moore equation. Its controlled terms contain only the original C²,α
bound and the density's C¹,α bound. The third-jet norm is multiplied by
an arbitrary small parameter, ready for compact-cover absorption. -/
theorem moore_interior_third_pointwise_schauder (hm : 3 ≤ m)
    (e : E ≃ₗᵢ[ℝ] V) {Γ K O : Set V} {hΓK : Γ ⊆ K}
    (hO : IsOpen O) (hKO : K ⊆ O) {α ell Λ R ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    (hΛ : 0 ≤ Λ) (hR : 0 ≤ R) (hρ : 0 < ρ)
    (x₀ : E) (hball : closedBall x₀ ρ ⊆ e ⁻¹' K) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ (u f : V → ℝ), ContDiff ℝ 4 u → DifferentiableOn ℝ f O →
      (∀ x ∈ O, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΓK α, ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ z : V, ell*‖z‖^2 ≤ inner ℝ z (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (e x₀)) z)) →
      (∀ z : V, inner ℝ z (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (e x₀)) z) ≤ Λ*‖z‖^2) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' K) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : e ⁻¹' K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x) →
      ∀ B, 0 ≤ B → (∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ B) →
      (∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ B*dist x y^α) →
      (∀ x ∈ closedBall x₀ δ, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x‖ ≤ ε*‖T‖+D*(B+R)) ∧
      (∀ x ∈ closedBall x₀ δ, ∀ y ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) y‖ ≤
          (ε*‖T‖+D*(B+R))*‖x-y‖^α) := by
  obtain ⟨N,hN,hcoefficient⟩ := exists_actual_moore_coefficient_bound (hΩK := hΓK) hα.le hR
  obtain ⟨δ,hδ,hlocal⟩ := interior_third_pointwise_schauder hm isOpen_empty
    (empty_subset (e ⁻¹' K)) hα hα1 hell hΛ hN hρ x₀ hball
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hestimate⟩ := hlocal ε hε
  refine ⟨D,hD,?_⟩
  intro u f hu hf heq U hUn hU₁ hU₂ hlower hupper T hT B hB hfn hfh
  let A : E → E →L[ℝ] E := fun y =>
    OAI.Analysis.PDE.Dirichlet.isometryConjugate e (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (e y)))
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let F : Fin m → E → ℝ := fun j y => OAI.Analysis.PDE.Dirichlet.directionalDerivative f (e (b j)) (e y)
  obtain ⟨hAn,hAh⟩ := hcoefficient u U hUn hU₂
  have hAs x : (A x).toLinearMap.IsSymmetric :=
    OAI.Analysis.PDE.Dirichlet.isometryConjugate_isSymmetric e _ (OAI.Analysis.PDE.Dirichlet.detRealOperator_isSymmetric _)
  have hAn' x (hx : x ∈ e ⁻¹' K) : ‖A x‖ ≤ N := by
    simpa only [A,OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate] using hAn (e x) hx
  have hAh' x (hx : x ∈ e ⁻¹' K) y (hy : y ∈ e ⁻¹' K) :
      ‖A x-A y‖ ≤ N*‖x-y‖^α := by
    simpa only [A,dist_eq_norm] using OAI.Analysis.PDE.Dirichlet.isometryConjugate_holder e
      (fun y => OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) hAh hx hy
  have hAl z : ell*‖z‖^2 ≤ inner ℝ z (A x₀ z) := by
    dsimp only [A]
    rw [real_inner_comm, OAI.Analysis.PDE.Dirichlet.inner_isometryConjugate, real_inner_comm]
    simpa only [e.norm_map] using hlower (e z)
  have hAu z : inner ℝ z (A x₀ z) ≤ Λ*‖z‖^2 := by
    dsimp only [A]
    rw [real_inner_comm, OAI.Analysis.PDE.Dirichlet.inner_isometryConjugate, real_inner_comm]
    simpa only [e.norm_map] using hupper (e z)
  obtain ⟨hDu,hD₂u⟩ := stored_pullback_first_second_bound e u (hu.of_le (by norm_num)) U hUn hU₁ hU₂
  apply hestimate A (fun x _ => hAs x) hAn' hAh' hAl hAu (u ∘ e) (hu.comp e.contDiff)
    F T hT B R hB hR hDu hD₂u
  · intro j x hx
    have hv : ‖e (b j)‖ = 1 := by rw [e.norm_map,b.norm_eq_one]
    exact ((fderiv ℝ f (e x)).le_opNorm (e (b j))).trans
      (by simpa only [hv,mul_one] using hfn (e x) hx)
  · intro j x hx y hy
    have hv : ‖e (b j)‖ = 1 := by rw [e.norm_map,b.norm_eq_one]
    have hb := (fderiv ℝ f (e x)-fderiv ℝ f (e y)).le_opNorm (e (b j))
    have hnorm := hfh (e x) hx (e y) hy
    have hb' : ‖F j x-F j y‖ ≤ ‖fderiv ℝ f (e x)-fderiv ℝ f (e y)‖ := by
      simpa only [F,OAI.Analysis.PDE.Dirichlet.directionalDerivative,sub_apply,hv,mul_one] using hb
    exact hb'.trans (by simpa only [e.isometry.dist_eq,dist_eq_norm] using hnorm)
  · intro j x hx
    exact moore_directional_equation_isometry_on_open e u f (hu.of_le (by norm_num))
      hO hf heq x (b j) (hKO hx)

end OAI.Analysis.PDE.Schauder
