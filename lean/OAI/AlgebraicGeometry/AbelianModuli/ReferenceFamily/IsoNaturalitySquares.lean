import Mathlib.CategoryTheory.Iso

/-! # Iso Naturality Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoNaturalitySquares

/-! Naturality squares survive inverse coordinates and conjugation. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] {X Y A B : C}

theorem iso_inverse_square (e : X ≅ A) (f : Y ≅ B) (a : X ⟶ Y) (b : A ⟶ B)
    (h : e.hom ≫ b = a ≫ f.hom) : e.inv ≫ a = b ≫ f.inv := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (e.inv ≫ a) = a := by simp only [Iso.hom_inv_id_assoc]
    _ = (a ≫ f.hom) ≫ f.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (e.hom ≫ b) ≫ f.inv := by rw [h]
    _ = e.hom ≫ (b ≫ f.inv) := Category.assoc _ _ _

theorem conjugateIso_natural (e : X ≅ A) (f : Y ≅ B) (a : X ⟶ Y) (b : A ⟶ B)
    (h : e.hom ≫ b = a ≫ f.hom) (u : X ≅ X) (v : Y ≅ Y)
    (huv : u.hom ≫ a = a ≫ v.hom) :
    (e.symm ≪≫ u ≪≫ e).hom ≫ b = b ≫ (f.symm ≪≫ v ≪≫ f).hom := by
  have hi := iso_inverse_square e f a b h
  change (e.inv ≫ (u.hom ≫ e.hom)) ≫ b = b ≫ (f.inv ≫ (v.hom ≫ f.hom))
  calc
    (e.inv ≫ (u.hom ≫ e.hom)) ≫ b = e.inv ≫ (u.hom ≫ (e.hom ≫ b)) := by rw [Category.assoc, Category.assoc]
    _ = e.inv ≫ (u.hom ≫ (a ≫ f.hom)) := by rw [h]
    _ = e.inv ≫ ((a ≫ v.hom) ≫ f.hom) := by rw [← Category.assoc u.hom, huv]
    _ = (e.inv ≫ a) ≫ (v.hom ≫ f.hom) := by simp only [Category.assoc]
    _ = (b ≫ f.inv) ≫ (v.hom ≫ f.hom) := by rw [hi]
    _ = b ≫ (f.inv ≫ (v.hom ≫ f.hom)) := Category.assoc _ _ _

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoNaturalitySquares
