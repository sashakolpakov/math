import OAI.Analysis.PDE.Schauder.Calculus.Interior.MoorePhysical
import OAI.Analysis.PDE.Schauder.Calculus.JetRestriction

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance globalThirdFirstGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance globalThirdFirstSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance globalThirdSecondGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance globalThirdSecondSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance globalThirdThirdGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance globalThirdThirdSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

/-- Localize the nonlinear interior estimate while retaining the global
third-jet norm. The equation is needed only on the open interior, not at
the boundary of the global jet domain. -/
theorem moore_interior_third_global_jet_schauder (hm : 3 ≤ m)
    (e : E ≃ₗᵢ[ℝ] V) {Γ K O : Set V} {hΓK : Γ ⊆ K}
    (hO : IsOpen O) (hOK : O ⊆ K) {α ell Λ R ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    (hΛ : 0 ≤ Λ) (hR : 0 ≤ R) (hρ : 0 < ρ)
    (x₀ : V) (hball : closedBall x₀ ρ ⊆ O) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ (u f : V → ℝ), ContDiff ℝ 4 u → DifferentiableOn ℝ f O →
      (∀ x ∈ O, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΓK α, ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ z : V, ell*‖z‖^2 ≤ inner ℝ z (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀) z)) →
      (∀ z : V, inner ℝ z (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀) z) ≤ Λ*‖z‖^2) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      ∀ B, 0 ≤ B → (∀ x ∈ O, ‖fderiv ℝ f x‖ ≤ B) →
      (∀ x ∈ O, ∀ y ∈ O, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ B*dist x y^α) →
      (∀ x ∈ closedBall x₀ δ, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ ε*‖T‖+D*(B+R)) ∧
      (∀ x ∈ closedBall x₀ δ, ∀ y ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          (ε*‖T‖+D*(B+R))*‖x-y‖^α) := by
  let S := closedBall x₀ ρ
  have hSK : S ⊆ K := hball.trans hOK
  obtain ⟨δ,hδ,hlocal⟩ := moore_interior_third_physical_schauder
    (hΓK := empty_subset S) hm e hO hball hα hα1 hell hΛ hR hρ x₀ (Subset.refl S)
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hestimate⟩ := hlocal ε hε
  refine ⟨D,hD,?_⟩
  intro u f hu hf heq U hUn hU₀ hU₁ hU₂ hlower hupper T hT B hB hfn hfh
  obtain ⟨U',hU'n,hU'₀,hU'₁,hU'₂⟩ := exists_actual_C2Holder_restriction hSK hα.le
    u (hu.of_le (by norm_num)) U hU₀ hU₁ hU₂
  obtain ⟨T',hT'n,hT'⟩ := exists_holder_restriction hSK hα.le T
  have hTactual (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value T' x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x := by
    rw [hT',hT]
  have hh := hestimate u f hu hf heq U' (hU'n.trans hUn) hU'₁ hU'₂ hlower hupper
    T' hTactual B hB (fun x hx => hfn x (hball hx))
    (fun x hx y hy => hfh x (hball hx) y (hball hy))
  have hbudget : ε*‖T'‖+D*(B+R) ≤ ε*‖T‖+D*(B+R) :=
    add_le_add (mul_le_mul_of_nonneg_left hT'n hε.le) le_rfl
  constructor
  · intro x hx
    exact (hh.1 x hx).trans hbudget
  · intro x hx y hy
    exact (hh.2 x hx y hy).trans
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
