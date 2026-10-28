import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Ideal Scalar Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.IdealScalarChange.ModuleIdealScalarChange

noncomputable section

/-! Canonical tensor coordinates for scalar extension of coefficient-ideal quotients. -/

open scoped TensorProduct

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] (I : Ideal R)

def equiv : ((S ⊗[R] M) ⧸ I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M))) ≃ₗ[S]
    S ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  TensorProduct.tensorQuotMapSMulEquivTensorQuot M S I

theorem equiv_mk_tmul (s : S) (m : M) :
    equiv R S M I (Submodule.Quotient.mk (s ⊗ₜ[R] m)) = s ⊗ₜ[R] Submodule.Quotient.mk m := by
  have hq : (Ideal.qoutMapEquivTensorQout S (I := I)) (1 : S ⧸ I.map (algebraMap R S)) =
      (1 : S) ⊗ₜ[R] (1 : R ⧸ I) := by
    change (TensorProduct.tensorQuotEquivQuotSMul S I).symm (Submodule.Quotient.mk (1 : S)) = _
    exact TensorProduct.tensorQuotEquivQuotSMul_symm_mk I 1
  simp [equiv, TensorProduct.tensorQuotMapSMulEquivTensorQuot, hq,
    LinearEquiv.baseChange_tmul, TensorProduct.smul_tmul']
  exact congrArg (fun x => s ⊗ₜ[R] x)
    ((TensorProduct.tensorQuotEquivQuotSMul M I).apply_symm_apply (Submodule.Quotient.mk m))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.IdealScalarChange.ModuleIdealScalarChange
