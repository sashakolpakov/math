import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Presentation
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Tensor Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorRelations

noncomputable section

/-! Quotient tensor products are represented by unit tensors. The
presentation criterion consequently has a direct ideal-membership form. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B]
variable (M : Type v) [AddCommGroup M] [Module B M]

theorem quotientTensor_exists_one_tmul (I : Ideal B) (x : (B ⧸ I) ⊗[B] M) :
    ∃ m : M, (1 : B ⧸ I) ⊗ₜ[B] m = x := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  obtain ⟨m, hm⟩ := (I • (⊤ : Submodule B M)).mkQ_surjective (e x)
  refine ⟨m, e.injective ?_⟩
  exact (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I m).trans hm

theorem quotientTensor_one_eq_zero_iff (I : Ideal B) (m : M) :
    (1 : B ⧸ I) ⊗ₜ[B] m = 0 ↔ m ∈ I • (⊤ : Submodule B M) := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  have he := TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I m
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact he.symm.trans ((congrArg e h).trans e.map_zero)
  · intro h
    apply e.injective
    rw [map_zero]
    exact he.trans ((Submodule.Quotient.mk_eq_zero _).mpr h)

theorem quotient_mk_zero_of_right_tensor_zero (I : Ideal B) (m : M)
    (h : m ⊗ₜ[B] (1 : B ⧸ I) = 0) :
    (I • (⊤ : Submodule B M)).mkQ m = 0 := by
  apply (TensorProduct.tensorQuotEquivQuotSMul M I).symm.injective
  rw [map_zero]
  exact h

variable {M}
variable {F : Type w} [AddCommGroup F] [Module B F] [Module.Flat B F]

theorem presentation_idealTensor_injective_iff_relation_mem
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I) ↔
      ∀ z : q.ker, z.val ∈ I • (⊤ : Submodule B F) →
        z ∈ I • (⊤ : Submodule B q.ker) := by
  rw [← IdealTensor.Presentation.presentation_tensor_quotient_injective_iff q hq I]
  constructor
  · intro h z hz
    apply (quotientTensor_one_eq_zero_iff q.ker I z).mp
    apply h
    rw [map_zero, LinearMap.lTensor_tmul]
    exact (quotientTensor_one_eq_zero_iff F I z.val).mpr hz
  · intro h
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨z, rfl⟩ := quotientTensor_exists_one_tmul q.ker I x
    apply (quotientTensor_one_eq_zero_iff q.ker I z).mpr
    apply h z
    exact (quotientTensor_one_eq_zero_iff F I z.val).mp hx

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorRelations
