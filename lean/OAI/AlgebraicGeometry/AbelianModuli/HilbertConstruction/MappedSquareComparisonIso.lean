import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ComparisonIsomorphism

/-! # Mapped Square Comparison Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedSquareComparisonIso

noncomputable section

/-! An ambient-square comparison becomes an isomorphism when its two vertical maps do. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

theorem isIso_mapped_pullbackLift_of_vert_isIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {A B X Y : C} (f : A ⟶ B) (a : A ⟶ X) (b : B ⟶ Y) (g : X ⟶ Y)
    (h : f ≫ b = a ≫ g) [HasPullback b g] [PreservesLimit (cospan b g) F]
    [IsIso (F.map a)] [IsIso (F.map b)] : IsIso (F.map (pullback.lift f a h)) := by
  have hR : IsPullback (F.map f) (F.map a) (F.map b) (F.map g) :=
    IsPullback.of_vert_isIso ⟨by rw [← F.map_comp, ← F.map_comp, h]⟩
  exact Pullback.ComparisonIsomorphism.isIso_comparison_of_pullbacks _ _ _ _ _ _ hR ((IsPullback.of_hasPullback b g).map F)
    (F.map (pullback.lift f a h))
    (by rw [← F.map_comp, pullback.lift_fst])
    (by rw [← F.map_comp, pullback.lift_snd])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedSquareComparisonIso
