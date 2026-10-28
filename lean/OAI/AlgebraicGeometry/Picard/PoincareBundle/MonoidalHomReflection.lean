import Mathlib.CategoryTheory.Monoidal.Mon

/-! # Monoidal Hom Reflection -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalHomReflection

/-! Faithful strong monoidal functors detect the group-law compatibility of an existing morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v u' v'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Faithful]
  {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)]

include F

/-- Both unit and multiplication equations are reflected through the faithful monoidal comparison. -/
theorem isMonHom : IsMonHom f where
  one_hom := F.map_injective <| by
    simpa [Functor.map_comp, cancel_epi] using IsMonHom.one_hom (F.map f)
  mul_hom := F.map_injective <| by
    simpa [Functor.map_comp, cancel_epi] using IsMonHom.mul_hom (F.map f)

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalHomReflection
