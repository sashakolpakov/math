import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Algebra.Basic

/-! # Compatible Scalar Tensor Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleScalarTensorMap

noncomputable section

/-! A coefficient-compatible ring action extends a linear map canonically to a tensor-product map. -/

universe u

variable {R B V G : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup V] [Module R V] [AddCommGroup G] [Module R G]
variable (ρ : B →+* Module.End R G)
variable (hρ : ∀ (r : R) (x : G), ρ (algebraMap R B r) x = r • x)

def compatibleScalarActionLinearMap : B →ₗ[R] G →ₗ[R] G where
  toFun := ρ
  map_add' := ρ.map_add
  map_smul' r b := by
    rw [Algebra.smul_def, map_mul]
    apply LinearMap.ext
    intro x
    exact hρ r (ρ b x)

def compatibleScalarTensorMap (a : V →ₗ[R] G) : TensorProduct R B V →ₗ[R] G :=
  TensorProduct.lift ((compatibleScalarActionLinearMap ρ hρ).compl₂ a)

theorem compatibleScalarTensorMap_tmul (a : V →ₗ[R] G) (b : B) (v : V) :
    compatibleScalarTensorMap ρ hρ a (b ⊗ₜ[R] v) = ρ b (a v) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleScalarTensorMap
