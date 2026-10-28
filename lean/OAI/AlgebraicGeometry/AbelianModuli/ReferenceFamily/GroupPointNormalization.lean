import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Point Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupPointNormalization

section

/-! Subtraction of a fixed group point is an actual morphism whose
effect on every test-scheme point is the literal group quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] {A : C} [GrpObj A]

def groupPointSubtract (p : 𝟙_ C ⟶ A) : A ⟶ A := 𝟙 A / (toUnit A ≫ p)

theorem groupPointSubtract_comp (p : 𝟙_ C ⟶ A) {T : C} (f : T ⟶ A) :
    f ≫ groupPointSubtract p = f / (toUnit T ≫ p) := by
  rw [groupPointSubtract, GrpObj.comp_div, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem groupPointSubtract_point (p : 𝟙_ C ⟶ A) : p ≫ groupPointSubtract p = 1 := by
  rw [groupPointSubtract_comp, toUnit_unit, Category.id_comp]
  exact div_self' p

end

section

/-! Translation by the value at the identity turns an actual
isomorphism of group-object carriers into an actual pointed isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] {A B : C} [GrpObj A] [GrpObj B]

def groupPointSubtractIso (p : 𝟙_ C ⟶ B) : B ≅ B where
  hom := groupPointSubtract p
  inv := 𝟙 B * (toUnit B ≫ p)
  hom_inv_id := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact div_mul_cancel (𝟙 B) (toUnit B ≫ p)
  inv_hom_id := by
    rw [groupPointSubtract_comp]
    exact mul_div_cancel_right (𝟙 B) (toUnit B ≫ p)

def groupPointNormalizedIso (e : A ≅ B) : A ≅ B :=
  e ≪≫ groupPointSubtractIso (η[A] ≫ e.hom)

theorem groupPointNormalizedIso_point (e : A ≅ B) :
    η[A] ≫ (groupPointNormalizedIso e).hom = η[B] := by
  change η[A] ≫ e.hom ≫ groupPointSubtract (η[A] ≫ e.hom) = η[B]
  rw [← Category.assoc, groupPointSubtract_point]
  rw [Hom.one_def, toUnit_unit, Category.id_comp]

end

/-! Identity normalization leaves the image of an isomorphism
unchanged under any monoidal functor when that image is already pointed. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    {A B : C} [GrpObj A] [GrpObj B]

theorem groupPointNormalizedIso_hom (e : A ≅ B) :
    (groupPointNormalizedIso e).hom = e.hom / ((1 : A ⟶ A) ≫ e.hom) := by
  change e.hom ≫ groupPointSubtract (η[A] ≫ e.hom) = _
  rw [groupPointSubtract_comp, Hom.one_def, Category.assoc]

theorem groupPointNormalizedIso_map (F : C ⥤ D) [F.Monoidal] (e : A ≅ B)
    (h : F.map ((1 : A ⟶ A) ≫ e.hom) = 1) :
    F.map (groupPointNormalizedIso e).hom = F.map e.hom := by
  rw [groupPointNormalizedIso_hom, div_eq_mul_inv, Functor.map_mul, Functor.map_inv', h, inv_one, mul_one]

theorem groupPointNormalizedIso_map_of_isMonHom (F : C ⥤ D) [F.Monoidal] (e : A ≅ B)
    [IsMonHom (F.map e.hom)] : F.map (groupPointNormalizedIso e).hom = F.map e.hom := by
  apply groupPointNormalizedIso_map F e
  rw [Functor.map_comp, Functor.map_one, MonObj.one_comp]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupPointNormalization
