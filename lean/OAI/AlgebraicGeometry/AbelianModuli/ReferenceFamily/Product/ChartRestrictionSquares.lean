import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

/-! # Chart Restriction Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRestrictionSquares

/-! Product charts commuting with inclusions into one ambient chart
also commute with intermediate restrictions. Their differences do too. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] (P : C ⥤ C)
    {U V X : C} (a : U ⟶ V) (b : V ⟶ X) (c : U ⟶ X)

theorem productChart_restriction_square [Mono (P.map b)] (hab : a ≫ b = c)
    (e : X ≅ P.obj X) (u : U ≅ P.obj U) (v : V ≅ P.obj V)
    (hu : u.hom ≫ P.map c = c ≫ e.hom) (hv : v.hom ≫ P.map b = b ≫ e.hom) :
    u.hom ≫ P.map a = a ≫ v.hom := by
  apply (cancel_mono (P.map b)).mp
  calc
    (u.hom ≫ P.map a) ≫ P.map b = u.hom ≫ P.map c := by
      rw [Category.assoc, ← P.map_comp, hab]
    _ = c ≫ e.hom := hu
    _ = (a ≫ b) ≫ e.hom := by rw [hab]
    _ = (a ≫ v.hom) ≫ P.map b := by simp only [Category.assoc, hv]

theorem productTransition_restriction_square
    {A B : C} (a : U ⟶ V) (b : A ⟶ B)
    (u u' : U ≅ A) (v v' : V ≅ B)
    (hu : u.hom ≫ b = a ≫ v.hom) (hv : u'.hom ≫ b = a ≫ v'.hom) :
    (u.symm ≪≫ u').hom ≫ b = b ≫ (v.symm ≪≫ v').hom := by
  change (u.inv ≫ u'.hom) ≫ b = b ≫ (v.inv ≫ v'.hom)
  apply (cancel_epi u.hom).mp
  calc
    u.hom ≫ ((u.inv ≫ u'.hom) ≫ b) = u'.hom ≫ b := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = a ≫ v'.hom := hv
    _ = (a ≫ v.hom) ≫ (v.inv ≫ v'.hom) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (u.hom ≫ b) ≫ (v.inv ≫ v'.hom) := by rw [hu]
    _ = u.hom ≫ (b ≫ (v.inv ≫ v'.hom)) := Category.assoc _ _ _

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartRestrictionSquares
