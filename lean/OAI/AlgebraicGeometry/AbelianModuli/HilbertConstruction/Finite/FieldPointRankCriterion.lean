import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AlgebraPointRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldPointCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Field Point Rank Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FieldPointRankCriterion

noncomputable section

/-! A finite scheme over a field is etale when its number of rational points equals its finite rank. Both quantities refer to the actual scheme and its canonical coordinate algebra. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem finiteFieldScheme_etale_of_point_card_eq
    {K : Type u} [Field K] (M : Over (Spec (.of K))) [IsFinite M.hom] (x : Spec (.of K))
    (hcard : Nat.card (Over.mk (𝟙 (Spec (.of K))) ⟶ M) = M.hom.finrank x) : Etale M.hom := by
  have : IsAffine M.left := isAffine_of_isAffineHom M.hom
  let B := Affine.OverChartPoints.affineOverAlgebra K M
  have : Module.Finite K B := Affine.FieldPointCoordinates.finiteAffineField_coordinateAlgebra_finite K M
  have hc : Nat.card (B →ₐ[K] K) = Module.finrank K B :=
    (Nat.card_congr (Affine.FieldPointCoordinates.affineFieldPointCoordinates K M)).symm.trans
      (hcard.trans (Affine.FieldPointCoordinates.finiteAffineField_finrank K M x))
  have hB : Algebra.Etale K B := AlgebraPointRank.finiteAlgebra_etale_of_point_card_eq K B hc
  have hE : Etale (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hB)
  exact (HilbertConstruction.Over.IsoMorphismProperty.overIso_morphismProperty_iff (@Etale) (Affine.OverChartPoints.affineOverIso K M)).mpr hE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FieldPointRankCriterion
