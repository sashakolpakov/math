import OAI.AlgebraicGeometry.ComplexMultiplication.SingularBaseChange
import Mathlib.Algebra.Module.LinearMap.Rat

/-! # Scalar Extension Object -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ScalarExtensionObject

noncomputable section

/-! # The scalar-extension object with the original rational scalar action -/

open _root_.CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- The tensor product in the change-of-rings functor identifies with the usual tensor
product through the identity on its complex coefficient factor. -/
def rationalComplexScalarsTensorEquiv (M : ModuleCat.{0} ℚ) :
    SingularBaseChange.rationalComplexScalars.obj M ≃ₗ[ℂ] ℂ ⊗[ℚ] M := by
  let A : ModuleCat ℚ :=
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (ModuleCat.of ℂ ℂ)
  let e : A ≃ₗ[ℂ] ℂ :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let : IsScalarTower ℚ ℂ A :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl ℚ M)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ScalarExtensionObject
