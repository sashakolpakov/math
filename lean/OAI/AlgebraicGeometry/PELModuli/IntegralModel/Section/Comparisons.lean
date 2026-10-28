import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.CoefficientModels

/-! # Comparisons -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons

noncomputable section

/-! Canonical sections and group laws under natural base-change
comparisons. Naturality retains the original specified base point. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]

def mappedSection (F : C ⥤ D) [F.Monoidal] {X : C} (x : 𝟙_ C ⟶ X) : 𝟙_ D ⟶ F.obj X :=
  Functor.LaxMonoidal.ε F ≫ F.map x

theorem mappedSection_naturality (F H : C ⥤ D) [F.Monoidal] [H.Monoidal]
    (c : F ⟶ H) {X : C} (x : 𝟙_ C ⟶ X) :
    mappedSection F x ≫ c.app X = mappedSection H x := by
  rw [mappedSection, Category.assoc, c.naturality, ← Category.assoc,
    NatTrans.IsMonoidal.unit]
  rfl

theorem mappedSection_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal]
    {X : C} (x : 𝟙_ C ⟶ X) :
    mappedSection G (mappedSection F x) = mappedSection (F ⋙ G) x := by
  simp only [mappedSection, Functor.map_comp, Functor.LaxMonoidal.comp_ε, Functor.comp_map,
    Category.assoc]

theorem mappedSection_one (F : C ⥤ D) [F.Monoidal] (X : C) [GrpObj X] :
    mappedSection F (1 : 𝟙_ C ⟶ X) = 1 := by
  simp only [mappedSection, F.map_one, MonObj.comp_one]

theorem mappedSection_comp_naturality
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (c : F ⋙ G ⟶ H) {X : C} (x : 𝟙_ C ⟶ X) :
    mappedSection G (mappedSection F x) ≫ c.app X = mappedSection H x := by
  rw [mappedSection_comp F G]
  exact mappedSection_naturality (F ⋙ G) H c x

theorem mappedSection_map (F : C ⥤ D) [F.Monoidal]
    {X Y : C} (x : 𝟙_ C ⟶ X) (f : X ⟶ Y) :
    mappedSection F x ≫ F.map f = mappedSection F (x ≫ f) := by
  simp only [mappedSection, F.map_comp, Category.assoc]

/-- A natural comparison from iterated pullback to direct pullback
preserves the actual group structure produced by iterated pullback. -/
theorem iterated_comparison_isMonHom
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal] (c : F ⋙ G ≅ H) (X : C) [GrpObj X] :
    letI : GrpObj (F.obj X) := Functor.grpObjObj (F := F) (G := X)
    letI : GrpObj (G.obj (F.obj X)) := Functor.grpObjObj (F := G) (G := F.obj X)
    IsMonHom (show G.obj (F.obj X) ⟶ H.obj X from (c.app X).hom) := by
  let e := (Functor.mapMonCompIso (F := F) (G := G)).symm.app (Mon.mk X) ≪≫
    (Functor.mapMonNatIso c).app (Mon.mk X)
  have he : e.hom.hom = (c.app X).hom := by
    change 𝟙 _ ≫ (c.app X).hom = _
    exact Category.id_comp _
  rw [← he]
  exact e.hom.isMonHom_hom

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons
