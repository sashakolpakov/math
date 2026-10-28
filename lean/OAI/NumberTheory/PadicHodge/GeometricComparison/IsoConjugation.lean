import Mathlib.CategoryTheory.Iso

/-! # Iso Conjugation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IsoConjugation.IsoConjugationSquare

/-! An identified conjugated map gives the original commuting square. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] {A B X Y : C}

theorem square (e : A ≅ X) (f : B ≅ Y) (a : A ⟶ B) (b : X ⟶ Y)
    (h : e.hom ≫ b ≫ f.inv = a) : a ≫ f.hom = e.hom ≫ b := by
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end OAI.NumberTheory.PadicHodge.GeometricComparison.IsoConjugation.IsoConjugationSquare
