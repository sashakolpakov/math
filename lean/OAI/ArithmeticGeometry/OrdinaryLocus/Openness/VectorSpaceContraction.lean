import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCocycles
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

/-! # Vector Space Contraction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.VectorSpaceContraction.Construction

noncomputable section

/-! Constructing the degree-zero contractions used in the Kunneth cocycle argument. -/

open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {C₀ : Type v} {C₁ : Type w}
    [AddCommGroup C₀] [Module k C₀] [AddCommGroup C₁] [Module k C₁]

theorem augmented_vectorSpace_contraction
    (u : k →ₗ[k] C₀) (e : C₀ →ₗ[k] k) (d : C₀ →ₗ[k] C₁)
    (he : e.comp u = LinearMap.id) (hexact : Function.Exact u d) :
    ∃ h : C₁ →ₗ[k] C₀, h.comp d = LinearMap.id - u.comp e := by
  let q : C₀ →ₗ[k] C₀ := LinearMap.id - u.comp e
  have hker : LinearMap.ker d ≤ LinearMap.ker q := by
    intro x hx
    obtain ⟨r, rfl⟩ := (hexact x).mp hx
    change u r - u (e (u r)) = 0
    have hr : e (u r) = r := LinearMap.congr_fun he r
    rw [hr, sub_self]
  let g := (LinearMap.ker d).liftQ q hker
  let r := g.comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨h, hh⟩ := r.exists_extend
  refine ⟨h, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hh ⟨d x, ⟨x, rfl⟩⟩
  change h (d x) = g (d.quotKerEquivRange.symm ⟨d x, ⟨x, rfl⟩⟩) at hx
  exact hx.trans (congrArg g (d.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩))

theorem augmented_exact_comp_zero
    (u : k →ₗ[k] C₀) (d : C₀ →ₗ[k] C₁) (hexact : Function.Exact u d) :
    d.comp u = 0 := by
  apply LinearMap.ext
  intro r
  exact (hexact (u r)).mpr ⟨r, rfl⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.VectorSpaceContraction.Construction
