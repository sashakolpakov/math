import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Mixed Complex Boundary Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MixedComplexBoundaryProjection

noncomputable section

/-! A vector-space complex admits a degree-one cochain projection
to its actual cycle quotient. The tensor of two such projections
annihilates the mixed part of every degree-two boundary. -/

open scoped TensorProduct

variable {k : Type*} [Field k]
    {C₀ C₁ C₂ : Type*} [AddCommGroup C₀] [Module k C₀]
    [AddCommGroup C₁] [Module k C₁] [AddCommGroup C₂] [Module k C₂]

def cycleBoundarySubmodule (d₀ : C₀ →ₗ[k] C₁) (d₁ : C₁ →ₗ[k] C₂) : Submodule k (LinearMap.ker d₁) :=
  (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype

def cycleClassProjection (d₀ : C₀ →ₗ[k] C₁) (d₁ : C₁ →ₗ[k] C₂) :
    C₁ →ₗ[k] ((LinearMap.ker d₁) ⧸ cycleBoundarySubmodule d₀ d₁) :=
  Classical.choose ((cycleBoundarySubmodule d₀ d₁).mkQ.exists_extend)

theorem cycleClassProjection_cycle (d₀ : C₀ →ₗ[k] C₁) (d₁ : C₁ →ₗ[k] C₂)
    (x : LinearMap.ker d₁) :
    cycleClassProjection d₀ d₁ x = (cycleBoundarySubmodule d₀ d₁).mkQ x :=
  LinearMap.congr_fun (Classical.choose_spec ((cycleBoundarySubmodule d₀ d₁).mkQ.exists_extend)) x

theorem cycleClassProjection_boundary (d₀ : C₀ →ₗ[k] C₁) (d₁ : C₁ →ₗ[k] C₂)
    (h : d₁.comp d₀ = 0) (x : C₀) : cycleClassProjection d₀ d₁ (d₀ x) = 0 := by
  let z : LinearMap.ker d₁ := ⟨d₀ x, LinearMap.congr_fun h x⟩
  exact (cycleClassProjection_cycle d₀ d₁ z).trans
    ((Submodule.Quotient.mk_eq_zero _).mpr (show z ∈ cycleBoundarySubmodule d₀ d₁ from ⟨x, rfl⟩))

theorem cycleClassProjection_comp (d₀ : C₀ →ₗ[k] C₁) (d₁ : C₁ →ₗ[k] C₂)
    (h : d₁.comp d₀ = 0) : (cycleClassProjection d₀ d₁).comp d₀ = 0 :=
  LinearMap.ext (cycleClassProjection_boundary d₀ d₁ h)

variable {D₀ D₁ D₂ : Type*} [AddCommGroup D₀] [Module k D₀]
    [AddCommGroup D₁] [Module k D₁] [AddCommGroup D₂] [Module k D₂]

theorem mixedComplexBoundary_projection_zero
    (dC₀ : C₀ →ₗ[k] C₁) (dC₁ : C₁ →ₗ[k] C₂) (hC : dC₁.comp dC₀ = 0)
    (dD₀ : D₀ →ₗ[k] D₁) (dD₁ : D₁ →ₗ[k] D₂) (hD : dD₁.comp dD₀ = 0)
    (a : C₁ ⊗[k] D₀) (b : C₀ ⊗[k] D₁) :
    TensorProduct.map (cycleClassProjection dC₀ dC₁) (cycleClassProjection dD₀ dD₁)
      (TensorProduct.map LinearMap.id dD₀ a - TensorProduct.map dC₀ LinearMap.id b) = 0 := by
  have ha : TensorProduct.map (cycleClassProjection dC₀ dC₁) (cycleClassProjection dD₀ dD₁)
      (TensorProduct.map LinearMap.id dD₀ a) = 0 := by
    induction a using TensorProduct.inductionOn with
    | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        cycleClassProjection_boundary dD₀ dD₁ hD, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have hb : TensorProduct.map (cycleClassProjection dC₀ dC₁) (cycleClassProjection dD₀ dD₁)
      (TensorProduct.map dC₀ LinearMap.id b) = 0 := by
    induction b using TensorProduct.inductionOn with
    | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        cycleClassProjection_boundary dC₀ dC₁ hC, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  rw [map_sub, ha, hb, sub_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MixedComplexBoundaryProjection
