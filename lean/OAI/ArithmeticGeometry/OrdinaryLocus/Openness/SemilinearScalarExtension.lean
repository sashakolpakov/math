import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Semilinear Scalar Extension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SemilinearScalarExtension.Construction

noncomputable section

/-! Extending a scalar-compatible additive map to a linear map on a tensor product. -/

open scoped TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

def semilinearScalarExtension (f : M →+ N)
    (hf : ∀ r m, f (r • m) = algebraMap R S r • f m) : S ⊗[R] M →ₗ[S] N := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N := {
    smul_assoc := fun r s n => by
      rw [Algebra.smul_def]
      exact mul_smul _ _ _ }
  refine TensorProduct.AlgebraTensorModule.lift {
    toFun := fun a => {
      toFun := fun m => a • f m
      map_add' := fun m n => by rw [map_add, smul_add]
      map_smul' := fun r m => by
        change a • f (r • m) = algebraMap R S r • (a • f m)
        rw [hf, smul_smul, smul_smul, mul_comm] }
    map_add' := fun a b => by
      apply LinearMap.ext
      intro m
      exact add_smul _ _ _
    map_smul' := fun a b => by
      apply LinearMap.ext
      intro m
      exact mul_smul _ _ _ }

theorem semilinearScalarExtension_tmul (f : M →+ N)
    (hf : ∀ r m, f (r • m) = algebraMap R S r • f m) (a : S) (m : M) :
    semilinearScalarExtension f hf (a ⊗ₜ[R] m) = a • f m := rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SemilinearScalarExtension.Construction
