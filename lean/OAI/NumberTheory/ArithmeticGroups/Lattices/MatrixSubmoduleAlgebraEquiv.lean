import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixFlatExtension

/-! # Matrix Submodule Algebra Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixSubmoduleAlgebraEquiv.Construction

noncomputable section

/-! Extending a matrix subspace is injective and identifies its tensor
product with the corresponding concrete matrix submodule. -/

open scoped Classical TensorProduct

def matrixSubmoduleAlgebraMap
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    R ⊗[k] W →ₗ[R] Matrix (Fin n) (Fin n) R :=
  (MatrixFlatExtension.Construction.matrixAlgebraExtension n).toLinearMap.comp (W.subtype.baseChange R)

theorem matrixSubmoduleAlgebraMap_tmul
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) (a : R) (A : W) :
    matrixSubmoduleAlgebraMap W (a ⊗ₜ[k] A) = a • A.val.map (algebraMap k R) := by
  change MatrixFlatExtension.Construction.matrixAlgebraExtension n (W.subtype.baseChange R (a ⊗ₜ[k] A)) = _
  rw [LinearMap.baseChange_tmul, MatrixFlatExtension.Construction.matrixAlgebraExtension_tmul]
  rfl

theorem matrixSubmoduleAlgebraMap_injective
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Function.Injective (matrixSubmoduleAlgebraMap (R := R) W) :=
  (MatrixFlatExtension.Construction.matrixAlgebraExtension n).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype W.injective_subtype)

theorem matrixSubmoduleAlgebraMap_range
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    (matrixSubmoduleAlgebraMap (R := R) W).range = MatrixFlatExtension.Construction.matrixSubmoduleAlgebraExtension (R := R) W :=
  LinearMap.range_comp _ _

def matrixSubmoduleAlgebraEquiv
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    R ⊗[k] W ≃ₗ[R] MatrixFlatExtension.Construction.matrixSubmoduleAlgebraExtension (R := R) W :=
  (LinearEquiv.ofInjective (matrixSubmoduleAlgebraMap W) (matrixSubmoduleAlgebraMap_injective W)).trans
    (LinearEquiv.ofEq _ _ (matrixSubmoduleAlgebraMap_range W))

theorem matrixSubmoduleAlgebraEquiv_coe
    {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) (x : R ⊗[k] W) :
    (matrixSubmoduleAlgebraEquiv W x).val = matrixSubmoduleAlgebraMap W x := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixSubmoduleAlgebraEquiv.Construction
