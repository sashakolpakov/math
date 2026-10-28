import Mathlib.Algebra.Category.Grp.Basic

/-! # Additive Iso Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.AdditiveIsoSquare

/-! # Inverses retain a commuting square of additive groups -/

open _root_.CategoryTheory

theorem additiveIsoSquare_inv_apply {A B C D : AddCommGrpCat}
    (e : A ≅ B) (f : C ≅ D) (a : A ⟶ C) (b : B ⟶ D)
    (h : a ≫ f.hom = e.hom ≫ b) (z : B) :
    f.inv (b z) = a (e.inv z) := by
  have hi : e.inv ≫ a = b ≫ f.inv := by
    apply (cancel_mono f.hom).mp
    simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ConcreteCategory.congr_hom hi z).symm

end OAI.AlgebraicGeometry.ComplexMultiplication.AdditiveIsoSquare
