import OAI.Analysis.PDE.Schauder.Calculus.Interior.MooreThird
import OAI.Analysis.PDE.Schauder.Calculus.ThirdHolderTransport

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance physicalThirdFirstGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFirstSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance physicalThirdSecondGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance physicalThirdSecondSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance physicalThirdThirdGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance physicalThirdThirdSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

/-- The full interior third-derivative estimate in the original physical
coordinates, with the original (not coordinate-dependent) third-jet norm. -/
theorem moore_interior_third_physical_schauder (hm : 3 ≤ m)
    (e : E ≃ₗᵢ[ℝ] V) {Γ K O : Set V} {hΓK : Γ ⊆ K}
    (hO : IsOpen O) (hKO : K ⊆ O) {α ell Λ R ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    (hΛ : 0 ≤ Λ) (hR : 0 ≤ R) (hρ : 0 < ρ)
    (x₀ : V) (hball : closedBall x₀ ρ ⊆ K) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ (u f : V → ℝ), ContDiff ℝ 4 u → DifferentiableOn ℝ f O →
      (∀ x ∈ O, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΓK α, ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ z : V, ell*‖z‖^2 ≤ inner ℝ z (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀) z)) →
      (∀ z : V, inner ℝ z (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀) z) ≤ Λ*‖z‖^2) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      ∀ B, 0 ≤ B → (∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ B) →
      (∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ B*dist x y^α) →
      (∀ x ∈ closedBall x₀ δ, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ ε*‖T‖+D*(B+R)) ∧
      (∀ x ∈ closedBall x₀ δ, ∀ y ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          (ε*‖T‖+D*(B+R))*‖x-y‖^α) := by
  have hball' : closedBall (e.symm x₀) ρ ⊆ e ⁻¹' K := by
    intro x hx
    apply hball
    have hd : dist (e x) x₀ = dist x (e.symm x₀) := by
      simpa only [e.apply_symm_apply] using e.isometry.dist_eq x (e.symm x₀)
    simpa only [mem_closedBall,hd] using hx
  obtain ⟨δ,hδ,hlocal⟩ := moore_interior_third_pointwise_schauder (hΓK := hΓK)
    hm e hO hKO hα hα1 hell hΛ hR hρ (e.symm x₀) hball'
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hestimate⟩ := hlocal ε hε
  refine ⟨D,hD,?_⟩
  intro u f hu hf heq U hUn hU₁ hU₂ hlower hupper T hT B hB hfn hfh
  obtain ⟨T',hT'n,hT'⟩ := exists_third_holder_isometry e hα.le u hu T hT
  have hh := hestimate u f hu hf heq U hUn hU₁ hU₂
    (by simpa only [e.apply_symm_apply] using hlower)
    (by simpa only [e.apply_symm_apply] using hupper) T' hT' B hB hfn hfh
  have hbudget : ε*‖T'‖+D*(B+R) ≤ ε*‖T‖+D*(B+R) :=
    add_le_add (mul_le_mul_of_nonneg_left hT'n hε.le) le_rfl
  have hin x (hx : x ∈ closedBall x₀ δ) : e.symm x ∈ closedBall (e.symm x₀) δ := by
    simpa only [mem_closedBall,e.symm.isometry.dist_eq] using hx
  have hu3 : ContDiff ℝ 3 u := hu.of_le (by norm_num)
  constructor
  · intro x hx
    have hx' := (hh.1 (e.symm x) (hin x hx)).trans hbudget
    simpa only [norm_third_isometry_comp e u hu3,e.apply_symm_apply] using hx'
  · intro x hx y hy
    have hxy := (hh.2 (e.symm x) (hin x hx) (e.symm y) (hin y hy)).trans
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))
    have hd : ‖e.symm x-e.symm y‖ = ‖x-y‖ := by rw [← map_sub,e.symm.norm_map]
    simpa only [norm_third_sub_isometry_comp e u hu3,e.apply_symm_apply,hd] using hxy

end OAI.Analysis.PDE.Schauder
