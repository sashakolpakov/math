import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Scalar Module Underlying Group -/

namespace OAI.Algebra.Modules.ScalarModuleUnderlyingGroup

noncomputable section

/-! The underlying additive group is retained under an induced scalar action. -/
open _root_.CategoryTheory
universe u
theorem addGroupOfCarrier (A : AddCommGrpCat.{u}) : AddCommGrpCat.of A = A := by
  cases A
  rfl

theorem scalarModuleUnderlyingGroup
    {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S)
    (A : AddCommGrpCat.{u}) (φ : S →+* End A) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
      ((ModuleCat.restrictScalars c).obj (ModuleCat.mkOfSMul φ)) = A := by
  cases A
  rfl
theorem scalarModuleUnderlyingGroup_smul
    {R S : Type u} [CommRing R] [CommRing S] (c : R →+* S)
    (A : AddCommGrpCat.{u}) (φ : S →+* End A) (r : R) :
    ((ModuleCat.restrictScalars c).obj (ModuleCat.mkOfSMul φ)).smul r ≫
      eqToHom ((scalarModuleUnderlyingGroup c A φ).trans (addGroupOfCarrier A).symm) =
    eqToHom ((scalarModuleUnderlyingGroup c A φ).trans (addGroupOfCarrier A).symm) ≫
      AddCommGrpCat.ofHom (φ (c r)).hom := by
  cases A
  rfl

end

end OAI.Algebra.Modules.ScalarModuleUnderlyingGroup
