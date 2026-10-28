import Mathlib.CategoryTheory.NatIso

/-! # Nat Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NatIso.NatIsoSectionSquare

/-! Transporting a composable section square through a natural isomorphism. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (b : X ⟶ Y)
  {M N Z : D} (a : M ⟶ N) (r : N ⟶ G.obj X) (c : M ⟶ F.obj X)
  (t : M ⟶ Z) (l : Z ⟶ F.obj Y)

theorem square (h₁ : a ≫ r = c ≫ (e.app X).hom) (h₂ : c ≫ F.map b = t ≫ l) :
    a ≫ r ≫ G.map b = t ≫ l ≫ (e.app Y).hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ G.map b) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => c ≫ k) (e.hom.naturality b).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ (e.app Y).hom) h₂).trans (Category.assoc _ _ _))))))

end OAI.NumberTheory.PadicHodge.GeometricComparison.NatIso.NatIsoSectionSquare
