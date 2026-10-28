import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Affine Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over an affine base, an ample bundle remains relatively ample after arbitrary base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X X' S T : Scheme.{u}} [IsAffine S]

theorem Line.Bundles.LineBundle.IsAmple.relativelyAmple_after_baseChange {L : Line.Bundles.LineBundle X}
    (hL : L.IsAmple) {a : X' ⟶ X} {p : X ⟶ S} {q : X' ⟶ T} {b : T ⟶ S}
    (H : IsPullback a q p b) : (L.pullback a).IsRelativelyAmple q := by
  intro U hU
  have : IsAffine U.toScheme := hU
  have H' : IsPullback ((q ⁻¹ᵁ U).ι ≫ a) (q ∣_ U) p (U.ι ≫ b) :=
    (isPullback_morphismRestrict q U).flip.paste_horiz H
  have : IsAffineHom ((q ⁻¹ᵁ U).ι ≫ a) :=
    MorphismProperty.of_isPullback H'.flip (inferInstance : IsAffineHom (U.ι ≫ b))
  exact (hL.pullback_of_isAffineHom ((q ⁻¹ᵁ U).ι ≫ a)).of_iso
    ((Scheme.Modules.pullbackComp (q ⁻¹ᵁ U).ι a).symm.app L.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
