import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Over Separated Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.OverSeparatedBase

noncomputable section

/-! An ample bundle is relatively ample for every morphism to a
separated scheme. Affine base opens have affine inverse-image inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affineOpen_inclusion_isAffine
    {Y : Scheme.{u}} [Y.IsSeparated] (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineHom U.ι := by
  constructor
  intro V hV
  apply U.ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact hU.inf hV

theorem ample_isRelativelyAmple_over_separated
    {X Y : Scheme.{u}} [Y.IsSeparated] (f : X ⟶ Y)
    {L : Line.Bundles.LineBundle X} (hL : L.IsAmple) : L.IsRelativelyAmple f := by
  intro U hU
  have : IsAffineHom U.ι := affineOpen_inclusion_isAffine U hU
  have : IsAffineHom (f ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U) ‹IsAffineHom U.ι›
  exact hL.pullback_of_isAffineHom (f ⁻¹ᵁ U).ι

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.OverSeparatedBase
