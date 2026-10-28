import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionEquivalence

/-! # Family Operation Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual operations on a pulled-back family are equivalent to a morphism from the pulled-back product, an endomorphism, and a family point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

@[ext] theorem FamilyGroup.Operations.FamilyGroupOperations.ext {S : Scheme.{u}} {X : Over S}
    (D E : FamilyGroup.Operations.FamilyGroupOperations X) (hu : D.unit = E.unit) (hm : D.mul = E.mul) (hi : D.inv = E.inv) : D = E := by
  cases D
  cases E
  cases hu
  cases hm
  cases hi
  rfl

def Intrinsic.FamilyOperationData.familyOperationDataEquiv {S : Scheme.{u}} (A T : Over S) :
    ((((Over.pullback T.hom).obj (A ⊗ A) ⟶ (Over.pullback T.hom).obj A) ×
       ((Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj A)) × (T ⟶ A)) ≃
      FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback T.hom).obj A) where
  toFun d :=
    { unit := Family.PointSectionEquivalence.familyPointSectionEquiv A T d.2
      mul := (Functor.Monoidal.μIso (Over.pullback T.hom) A A).hom ≫ d.1.1
      inv := d.1.2 }
  invFun D :=
    (((Functor.Monoidal.μIso (Over.pullback T.hom) A A).inv ≫ D.mul, D.inv),
      (Family.PointSectionEquivalence.familyPointSectionEquiv A T).symm D.unit)
  left_inv d := by
    apply Prod.ext
    · apply Prod.ext
      · exact Iso.inv_hom_id_assoc _ _
      · rfl
    · exact (Family.PointSectionEquivalence.familyPointSectionEquiv A T).symm_apply_apply d.2
  right_inv D := by
    apply FamilyGroup.Operations.FamilyGroupOperations.ext
    · exact (Family.PointSectionEquivalence.familyPointSectionEquiv A T).apply_symm_apply D.unit
    · exact Iso.hom_inv_id_assoc _ _
    · rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
