import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ClosedImageRestriction

/-! # Closed Open Intermediate -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ClosedOpenIntermediate.Construction

noncomputable section

/-! An intermediate closed subscheme with the exact open restriction contains that open as an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def closedOpenIntermediateMap {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y)
    (L : Y.IdealSheafData) (hL : L ≤ (i ≫ j).ker) : Z ⟶ L.subscheme :=
  (i ≫ j).toImage ≫ Scheme.IdealSheafData.inclusion hL

theorem closedOpenIntermediateMap_over {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y)
    (L : Y.IdealSheafData) (hL : L ≤ (i ≫ j).ker) :
    closedOpenIntermediateMap i j L hL ≫ L.subschemeι = i ≫ j := by
  rw [closedOpenIntermediateMap, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  exact (i ≫ j).toImage_imageι

theorem closedOpenIntermediateMap_isPullback {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y)
    [IsClosedImmersion i] (L : Y.IdealSheafData) (hL : L ≤ (i ≫ j).ker)
    (he : L.comap j = i.ker) :
    IsPullback (closedOpenIntermediateMap i j L hL) i L.subschemeι j := by
  apply IsPullback.flip
  apply isPullback_of_isClosedImmersion i L.subschemeι (closedOpenIntermediateMap i j L hL) j
    (closedOpenIntermediateMap_over i j L hL).symm
  rwa [Scheme.IdealSheafData.ker_subschemeι]

theorem closedOpenIntermediateMap_isOpenImmersion {Z W Y : Scheme.{u}} (i : Z ⟶ W) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsOpenImmersion j] (L : Y.IdealSheafData) (hL : L ≤ (i ≫ j).ker)
    (he : L.comap j = i.ker) : IsOpenImmersion (closedOpenIntermediateMap i j L hL) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (closedOpenIntermediateMap_isPullback i j L hL he).flip inferInstance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ClosedOpenIntermediate.Construction
