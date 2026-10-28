/-
Derived from Formal Conjectures:
  HodgeConjecture/Mathlib/LinearAlgebra/Dual/Defs.lean
The upstream Formal Conjectures repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Dual Defs -/

namespace OAI.LinearAlgebra.Foundations.DualDefs

/-- The dual of the zero map is zero. -/
@[simp]
theorem LinearMap.dualMap_zero {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] : (0 : M₁ →ₗ[R] M₂).dualMap = 0 := by
  rw [LinearMap.dualMap_def, map_zero]

/-- The dual of a sum of maps is the sum of the duals. -/
theorem LinearMap.dualMap_add {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (f g : M₁ →ₗ[R] M₂) :
    (f + g).dualMap = f.dualMap + g.dualMap := by
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def, LinearMap.dualMap_def, map_add]

/-- The dual of a difference of maps is the difference of the duals. -/
theorem LinearMap.dualMap_sub {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (f g : M₁ →ₗ[R] M₂) :
    (f - g).dualMap = f.dualMap - g.dualMap := by
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def, LinearMap.dualMap_def, map_sub]

/-- The dual of a split injection is surjective: extend a functional by precomposing with the
retraction. Over a field use `LinearMap.dualMap_surjective_of_injective`, which needs no
splitting. -/
theorem LinearMap.dualMap_surjective_of_comp_eq_id {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₁} (h : g.comp f = LinearMap.id) :
    Function.Surjective f.dualMap :=
  fun φ => ⟨φ.comp g, LinearMap.ext fun x => congrArg φ (LinearMap.congr_fun h x)⟩

end OAI.LinearAlgebra.Foundations.DualDefs
