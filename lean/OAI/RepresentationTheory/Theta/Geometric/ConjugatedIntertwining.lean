import Mathlib.CategoryTheory.Iso

/-! # Conjugated Intertwining -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConjugatedIntertwining

/-! Compose a commuting square with the actual target presentation. -/

open _root_.CategoryTheory

theorem conjugated_intertwining {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (e : Y ≅ Z) (a : X ⟶ X) (b : Y ⟶ Y)
    (h : a ≫ f = f ≫ b) :
    a ≫ (f ≫ e.hom) = (f ≫ e.hom) ≫ (e.inv ≫ b ≫ e.hom) := by
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end OAI.RepresentationTheory.Theta.Geometric.ConjugatedIntertwining
