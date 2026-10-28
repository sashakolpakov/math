import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationMonoids

/-! # Presheaf Monoid Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafMonoidSections

noncomputable section

/-! Sections of a set-valued commutative monoid presheaf inherit its multiplication and restriction homomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe v u w

variable {C : Type u} [Category.{v} C]

abbrev presheafSectionsCommMonoid (F : C ⥤ Type w) [MonObj F] [IsCommMonObj F]
    (T : C) : CommMonoid (F.obj T) := by
  letI : MonObj (F.obj T) := (Monoidal.MonFunctorCategoryEquivalence.functorObjObj F T).mon
  letI : IsCommMonObj (F.obj T) := ⟨congr_app (IsCommMonObj.mul_comm F) T⟩
  exact CommMonTypeEquivalenceCommMon.commMonCommMonoid (F.obj T)

theorem presheafSections_map_one (F : C ⥤ Type w) [MonObj F] [IsCommMonObj F]
    {T U : C} (f : T ⟶ U) :
    letI := presheafSectionsCommMonoid F T
    letI := presheafSectionsCommMonoid F U
    F.map f 1 = 1 := by
  exact (ConcreteCategory.congr_hom (CC := fun X : Type w => X) ((MonObj.one (X := F)).naturality f) PUnit.unit).symm

theorem presheafSections_map_mul (F : C ⥤ Type w) [MonObj F] [IsCommMonObj F]
    {T U : C} (f : T ⟶ U) (a b : F.obj T) :
    letI := presheafSectionsCommMonoid F T
    letI := presheafSectionsCommMonoid F U
    F.map f (a * b) = F.map f a * F.map f b := by
  exact (ConcreteCategory.congr_hom (CC := fun X : Type w => X) ((MonObj.mul (X := F)).naturality f) (a, b)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafMonoidSections
