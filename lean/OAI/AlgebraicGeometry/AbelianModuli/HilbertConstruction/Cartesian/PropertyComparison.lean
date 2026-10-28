import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Property Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison

noncomputable section

/-! A base-change-stable morphism property can be checked on any actual Cartesian model or on the categorical pullback, equivalently. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem property_cartesian_iff_pullback (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) : P p ↔ P (pullback.snd f c) := by
  constructor
  · intro hp
    have hi : IsPullback h.isoPullback.inv (pullback.snd f c) p (𝟙 T) :=
      IsPullback.of_horiz_isIso ⟨h.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
    exact MorphismProperty.of_isPullback (P := P) hi hp
  · intro hp
    have hi : IsPullback h.isoPullback.hom p (pullback.snd f c) (𝟙 T) :=
      IsPullback.of_horiz_isIso ⟨h.isoPullback_hom_snd.trans (Category.comp_id _).symm⟩
    exact MorphismProperty.of_isPullback (P := P) hi hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison
