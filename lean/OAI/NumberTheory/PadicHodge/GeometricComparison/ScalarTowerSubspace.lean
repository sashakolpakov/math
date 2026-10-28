import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarExtension
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar Tower Subspace -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTowerSubspace.ScalarTowerComparison

noncomputable section

/-! The canonical tensor associativity comparison preserves the actual scalar-extended operators and subspaces. -/

open scoped TensorProduct

variable (K A L : Type*) [Field K] [Field A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsScalarTower K A L]
  {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def equiv (V : Type*) [AddCommGroup V] [Module K V] :
    L ⊗[A] (A ⊗[K] V) ≃ₗ[L] L ⊗[K] V :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange K A L L V

theorem naturality (f : V →ₗ[K] W) :
    (equiv K A L W).toLinearMap.comp ((f.baseChange A).baseChange L) =
      (f.baseChange L).comp (equiv K A L V).toLinearMap :=
  (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange K A L (M := L) f).symm

theorem subspace (P : Submodule K V) :
    ((P.baseChange A).baseChange L).map (equiv K A L V).toLinearMap = P.baseChange L := by
  have hP : (P.baseChange A).baseChange L = ((P.subtype.baseChange A).baseChange L).range :=
    ScalarExtension.ScalarExtensionRanges.range L (P.subtype.baseChange A)
  rw [hP, ← LinearMap.range_comp, naturality]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (equiv K A L P).surjective)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTowerSubspace.ScalarTowerComparison
