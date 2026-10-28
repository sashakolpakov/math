import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Integral Scalar Unit -/

namespace OAI.AlgebraicTopology.Products.IntegralScalarUnit

noncomputable section

/-!
# The tensor unit for extension of integral coefficients

The scalar structure is induced by the same integer ring homomorphism as
`ModuleCat.extendScalars`, so the native tensor-unit equivalence is linear
for the actual coefficient extension.
-/

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extension of the rank-one integral module is the coefficient ring. -/
def integralScalarUnitIso (R : Type) [CommRing R] :
    (ModuleCat.extendScalars (Int.castRingHom R)).obj (ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of R R := by
  letI : Algebra ℤ R := (Int.castRingHom R).toAlgebra
  letI : Module ℤ R := Module.compHom R (Int.castRingHom R)
  letI : SMul ℤ R := (Module.compHom R (Int.castRingHom R)).toSMul
  letI : IsScalarTower ℤ R R := IsScalarTower.of_compHom ℤ R R
  letI : SMulCommClass ℤ R R := SMulCommClass.of_commMonoid ℤ R R
  exact (TensorProduct.AlgebraTensorModule.rid ℤ R R).toModuleIso

/-- The actual tensor-unit map multiplies the scalar and the integer. -/
@[simp]
theorem integralScalarUnitIso_hom_tmul (R : Type) [CommRing R] (r : R) (z : ℤ) :
    (integralScalarUnitIso R).hom (r ⊗ₜ[ℤ, Int.castRingHom R] z) = r * (z : R) := by
  change (z : R) * r = r * (z : R)
  exact mul_comm _ _

end

end OAI.AlgebraicTopology.Products.IntegralScalarUnit
