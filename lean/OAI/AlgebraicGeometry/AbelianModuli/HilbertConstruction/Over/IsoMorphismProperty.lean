import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison

/-! # Iso Morphism Property -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty

noncomputable section

/-! Morphism properties stable under base change are invariant under isomorphism of families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem overIso_morphismProperty_iff (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    P X.hom ↔ P Y.hom := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  constructor
  · exact MorphismProperty.of_isPullback (P := P)
      (IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩)
  · exact MorphismProperty.of_isPullback (P := P)
      (IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoMorphismProperty
