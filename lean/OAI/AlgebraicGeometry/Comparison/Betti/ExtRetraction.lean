import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Ext Retraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtRetraction

noncomputable section

/-! Higher Ext vanishing passes to a genuine retraction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_retraction (A : C) {F G : C}
    (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F) (n : ℕ)
    [Subsingleton (Ext A G n)] : Subsingleton (Ext A F n) := by
  let H := (extFunctor.{w} n : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : Subsingleton (H.obj G) := inferInstanceAs (Subsingleton (Ext A G n))
  have h : H.map i ≫ H.map r = 𝟙 _ := by
    rw [← H.map_comp, hir, H.map_id]
  have hl : Function.LeftInverse (H.map r) (H.map i) :=
    fun a => ConcreteCategory.congr_hom h a
  exact hl.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtRetraction
