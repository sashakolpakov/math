import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarRestriction.ScalarRestrictionIdentity

noncomputable section

/-! Restriction of scalars along an algebra map agrees with an already compatible module action. -/

open _root_.CategoryTheory

universe u v

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (M : Type v) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

def ofModuleEq (P Q : Module R M) (h : P = Q) :
    @ModuleCat.of R _ M _ P ≅ @ModuleCat.of R _ M _ Q := by
  cases h
  exact Iso.refl _

omit [Module R M] in
theorem ofModuleEq_hom_apply (P Q : Module R M) (h : P = Q) (m : M) :
    (ofModuleEq R M P Q h).hom m = m := by
  cases h
  rfl

theorem module_eq : (inferInstance : Module R M) = Module.compHom M (algebraMap R A) :=
  Module.ext' _ _ (fun r m => (IsScalarTower.algebraMap_smul A r m).symm)

def iso : ModuleCat.of R M ≅
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M) :=
  ofModuleEq R M _ _ (module_eq R A M)

theorem iso_hom_apply (m : M) : (iso R A M).hom m = m :=
  ofModuleEq_hom_apply R M _ _ (module_eq R A M) m

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarRestriction.ScalarRestrictionIdentity
