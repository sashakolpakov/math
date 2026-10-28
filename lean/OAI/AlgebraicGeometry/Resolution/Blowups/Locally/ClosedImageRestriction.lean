import OAI.AlgebraicGeometry.Resolution.Blowups.Open.IdealSheafBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBlowupSmoothGluing
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Closed Image Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ClosedImageRestriction.Construction

noncomputable section

/-! The actual scheme image of a closed subscheme in an open set recovers that subscheme on the same open set. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem kernel_comap_of_comp_open
    {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y) [IsOpenImmersion j] [QuasiCompact (i ≫ j)] :
    (i ≫ j).ker.comap j = i.ker := by
  have hp : IsPullback (𝟙 Z) i (i ≫ j) j := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback
    · simp only [Category.id_comp]
    · ext z
      constructor
      · intro _
        exact ⟨z, rfl⟩
      · intro _
        exact ⟨i z, rfl⟩
  exact Open.IdealSheafBaseChange.Construction.kernel_comap_of_open_pullback (i ≫ j) i (𝟙 Z) j hp.flip

theorem closed_open_image_isPullback
    {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact (i ≫ j)] :
    IsPullback (i ≫ j).toImage i (i ≫ j).imageι j := by
  apply IsPullback.flip
  apply isPullback_of_isClosedImmersion i (i ≫ j).imageι (i ≫ j).toImage j
    (i ≫ j).toImage_imageι.symm
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
  exact kernel_comap_of_comp_open i j

theorem closed_open_image_opensRange
    {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact (i ≫ j)] :
    (i ≫ j).toImage.opensRange = (i ≫ j).imageι ⁻¹ᵁ j.opensRange :=
  SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (i ≫ j).toImage i (i ≫ j).imageι j (closed_open_image_isPullback i j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ClosedImageRestriction.Construction
