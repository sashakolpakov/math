import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Product Map Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductMapProjections

noncomputable section

/-! Tensoring a product of linear maps commutes with both target projections. -/

universe u v w z t

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type z} [AddCommGroup P] [Module R P]
variable (A : Type t) [AddCommGroup A] [Module R A]

theorem tensor_productMap_fst (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    ((LinearMap.fst R N P).lTensor A).comp ((f.prod g).lTensor A) = f.lTensor A := by
  rw [← LinearMap.lTensor_comp]
  rfl

theorem tensor_productMap_snd (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    ((LinearMap.snd R N P).lTensor A).comp ((f.prod g).lTensor A) = g.lTensor A := by
  rw [← LinearMap.lTensor_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductMapProjections
