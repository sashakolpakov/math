import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Base Change Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BaseChangeQuotient

noncomputable section

/-! Quotient scalar extension with the original map and its exact kernel. -/

universe u v w

variable (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) (N : Type w)
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N]
  (f : M →ₗ[R] N) (hf : IsBaseChange (R ⧸ I) f)

def equiv : (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R] N :=
  (TensorProduct.quotTensorEquivQuotSMul M I).symm.trans (hf.equiv.restrictScalars R)

theorem equiv_mk (x : M) : BaseChangeQuotient.equiv R I M N f hf (Submodule.Quotient.mk x) = f x := by
  change hf.equiv ((TensorProduct.quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk x)) = f x
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, IsBaseChange.equiv_tmul, one_smul]

include hf in
theorem surjective : Function.Surjective f := by
  intro y
  obtain ⟨a, rfl⟩ := (BaseChangeQuotient.equiv R I M N f hf).surjective y
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R M).mkQ_surjective a
  exact ⟨x, (equiv_mk R I M N f hf x).symm⟩

include hf in
theorem kernel : LinearMap.ker f = I • ⊤ := by
  ext x
  change f x = 0 ↔ x ∈ (I • ⊤ : Submodule R M)
  rw [← equiv_mk R I M N f hf x, ← (BaseChangeQuotient.equiv R I M N f hf).map_zero,
    (BaseChangeQuotient.equiv R I M N f hf).injective.eq_iff]
  exact Submodule.Quotient.mk_eq_zero (p := I • ⊤) (x := x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BaseChangeQuotient
