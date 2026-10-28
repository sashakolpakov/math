import Mathlib

/-! # Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ScalarExtension

noncomputable section

/-! The canonical map extending a linear map to a larger scalar field. -/

open scoped TensorProduct
variable {R S D M : Type*} [Field R] [Field S] [Algebra R S]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

def extend (f : D →ₗ[R] M) : S ⊗[R] D →ₗ[S] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun d => a • f d
          map_add' := fun x y => by rw [map_add, smul_add]
          map_smul' := fun c d => by
            change a • f (c • d) = c • (a • f d)
            rw [map_smul, smul_comm] }
      map_add' := fun a b => LinearMap.ext fun d => add_smul a b (f d)
      map_smul' := fun a b => LinearMap.ext fun d => mul_smul a b (f d) }

theorem extend_tmul (f : D →ₗ[R] M) (a : S) (d : D) : extend f (a ⊗ₜ[R] d) = a • f d := rfl

theorem extend_one_tmul (f : D →ₗ[R] M) (d : D) : extend f ((1 : S) ⊗ₜ[R] d) = f d := by
  rw [extend_tmul, one_smul]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ScalarExtension
