import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Mapped Comparison Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComparisonPullback

noncomputable section

/-! A functor carries a comparison square to a pullback once it makes the comparison an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

theorem isPullback_of_mapped_comparison_isIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {P Q A B Z : C} (p : P ⟶ A) (q : P ⟶ B) (f : A ⟶ Z) (g : B ⟶ Z)
    [PreservesLimit (cospan f g) F] (h : IsPullback p q f g)
    (c : Q ⟶ P) (i : Q ⟶ A) (j : Q ⟶ B) (hi : c ≫ p = i) (hj : c ≫ q = j)
    [IsIso (F.map c)] : IsPullback (F.map i) (F.map j) (F.map f) (F.map g) := by
  apply (h.map F).of_iso' (asIso (F.map c)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, ← F.map_comp] using congrArg F.map hi
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, ← F.map_comp] using congrArg F.map hj
  · simp
  · simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComparisonPullback
