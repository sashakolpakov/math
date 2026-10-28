import Mathlib.CategoryTheory.Functor.Category

/-! # Functor Return Isomorphism -/

namespace OAI.CategoryTheory.Functors.FunctorReturnIsomorphism

noncomputable section

open _root_.CategoryTheory
universe u v u' v'
def functorReturnMap {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (F : C ⥤ D) {X Y : C} {Z : D} (j : X ⟶ Y) (k : Z ≅ F.obj Y) :
    F.obj X ⟶ Z := F.map j ≫ k.inv

def functorReturnIso {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (F : C ⥤ D) {X Y : C} {Z : D} (e : X ≅ Y) (k : Z ≅ F.obj Y) :
    F.obj X ≅ Z where
  hom := functorReturnMap F e.hom k
  inv := k.hom ≫ F.map e.inv
  hom_inv_id := (F.mapIso e ≪≫ k.symm).hom_inv_id
  inv_hom_id := (F.mapIso e ≪≫ k.symm).inv_hom_id

theorem functorReturnIso_hom {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (F : C ⥤ D) {X Y : C} {Z : D} (e : X ≅ Y) (k : Z ≅ F.obj Y) :
    (functorReturnIso F e k).hom = functorReturnMap F e.hom k := rfl

end

end OAI.CategoryTheory.Functors.FunctorReturnIsomorphism
