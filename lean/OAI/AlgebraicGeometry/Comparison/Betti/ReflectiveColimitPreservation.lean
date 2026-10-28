import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Reflective Colimit Preservation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ReflectiveColimitPreservation.Category

noncomputable section

/-! Colimit preservation descends along a reflective presentation of every target object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃ w w'

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {J : Type w} [Category.{w'} J]

theorem preservesColimit_image_of_composite (K : J ⥤ A) (F : A ⥤ B) (G : B ⥤ C)
    [HasColimit K] [PreservesColimit K F] [PreservesColimit K (F ⋙ G)] :
    PreservesColimit (K ⋙ F) G :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves F (colimit.isColimit K))
    (isColimitOfPreserves (F ⋙ G) (colimit.isColimit K))

theorem preservesColimitsOfShape_of_reflective (F : A ⥤ B) (R : B ⥤ A) (G : B ⥤ C)
    (e : R ⋙ F ≅ 𝟭 B) [HasColimitsOfShape J A]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J (F ⋙ G)] :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := by
    let : PreservesColimit ((K ⋙ R) ⋙ F) G := preservesColimit_image_of_composite (K ⋙ R) F G
    exact preservesColimit_of_iso_diagram G
      (Functor.associator K R F ≪≫ Functor.isoWhiskerLeft K e ≪≫ Functor.rightUnitor K)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ReflectiveColimitPreservation.Category
