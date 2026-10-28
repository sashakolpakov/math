import Mathlib.CategoryTheory.Iso

/-! # Coordinate Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoordinateSquare.Comparison

/-! A comparison square is preserved when the two source objects are expressed in isomorphic coordinates. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
  {A A' B B' U V : C} (e : A ≅ A') (d : B ≅ B')
  (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ U) (b : B ⟶ V) (g : U ⟶ V)

theorem conjugate (hcoord : f ≫ d.hom = e.hom ≫ f') (hcmp : f ≫ b = a ≫ g) :
    f' ≫ (d.inv ≫ b) = (e.inv ≫ a) ≫ g := by
  apply (cancel_epi e.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc e.hom f', ← hcoord]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hcmp

theorem map_postcompose {D : Type*} [Category D] (H : C ⥤ D)
    {P K L L' : C} {W : D} (a : P ⟶ K) (b : K ⟶ L) (e : L ≅ L')
    (c : H.obj K ⟶ W) (d : H.obj L ⟶ W) (h : H.map b ≫ d = c) :
    H.map (a ≫ b ≫ e.hom) ≫ (H.map e.inv ≫ d) = H.map a ≫ c := by
  have he : H.map e.hom ≫ H.map e.inv ≫ d = d :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ d) (H.map_comp e.hom e.inv).symm).trans
        ((congrArg (fun f => H.map f ≫ d) e.hom_inv_id).trans
          ((congrArg (fun f => f ≫ d) (H.map_id L)).trans (Category.id_comp d))))
  rw [H.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [he, h]

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoordinateSquare.Comparison
