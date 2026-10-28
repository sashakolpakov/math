import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor Scalar Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.TensorScalarChange

noncomputable section

/-! Tensoring over a quotient coefficient ring agrees with tensoring over the original ring. The comparison is linear over the final scalar algebra and commutes with the actual base-changed linear maps. -/
open scoped TensorProduct
universe u

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

theorem tensor_compatibleSMul_of_surjective_algebraMap
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module B M] [IsScalarTower R B M]
    [Module R N] [Module B N] [IsScalarTower R B N]
    (h : Function.Surjective (algebraMap R B)) : TensorProduct.CompatibleSMul R B M N where
  smul_tmul b m n := by
    obtain ⟨r, rfl⟩ := h b
    simpa only [IsScalarTower.algebraMap_smul] using
      (TensorProduct.smul_tmul r m n : (r • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n))

variable (h : Function.Surjective (algebraMap R B))
variable (M : Type u) [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]

def quotientTensorScalarEquiv : C ⊗[R] M ≃ₗ[C] C ⊗[B] M := by
  let : TensorProduct.CompatibleSMul R B C M := tensor_compatibleSMul_of_surjective_algebraMap h
  exact TensorProduct.equivOfCompatibleSMul B R C C M

theorem quotientTensorScalarEquiv_tmul (c : C) (m : M) :
    quotientTensorScalarEquiv (C := C) h M (c ⊗ₜ[R] m) = c ⊗ₜ[B] m := rfl

theorem quotientTensorScalarEquiv_naturality
    {N : Type u} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
    (f : M →ₗ[B] N) (z : C ⊗[R] M) :
    quotientTensorScalarEquiv (C := C) h N ((f.restrictScalars R).baseChange C z) =
      f.baseChange C (quotientTensorScalarEquiv (C := C) h M z) := by
  induction z with
  | tmul c m => rfl
  | add z w hz hw => simp only [map_add, hz, hw]

variable (N : Type u) [AddCommGroup N] [Module R N]

def quotientDoubleTensorEquiv : C ⊗[R] (B ⊗[R] N) ≃ₗ[C] C ⊗[R] N :=
  quotientTensorScalarEquiv (C := C) h (B ⊗[R] N) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R B C C N

theorem quotientDoubleTensorEquiv_tmul (c : C) (b : B) (n : N) :
    quotientDoubleTensorEquiv (C := C) h N (c ⊗ₜ[R] (b ⊗ₜ[R] n)) =
      (b • c) ⊗ₜ[R] n := rfl

theorem quotientDoubleTensorEquiv_naturality
    {V W : Type u} [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (f : V →ₗ[R] W) (z : C ⊗[R] (B ⊗[R] V)) :
    quotientDoubleTensorEquiv (C := C) h W (((f.baseChange B).restrictScalars R).baseChange C z) =
      f.baseChange C (quotientDoubleTensorEquiv (C := C) h V z) := by
  induction z with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    induction x with
    | tmul b v => rfl
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.TensorScalarChange
