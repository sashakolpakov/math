import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AffineCover

/-! # Base Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseFunctoriality

noncomputable section

/-! The explicit relative projective base maps preserve identities and composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem relativeProjectiveBaseMap_id (S : Scheme.{u}) (n : ℕ) :
    BaseMaps.relativeProjectiveBaseMap (𝟙 S) n = 𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S n).left := by
  apply (Projective.AffineCover.projectiveAffineOpenCover S.affineOpenCover n).hom_ext
  intro i
  change AffineProjective.Charts.affineProjectiveChartMap (S.affineOpenCover.f i) n ≫ BaseMaps.relativeProjectiveBaseMap (𝟙 S) n = _
  rw [BaseMaps.relativeProjectiveBaseMap_affine, Category.comp_id, Category.comp_id]
  rfl

theorem relativeProjectiveBaseMap_comp {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T) (n : ℕ) :
    BaseMaps.relativeProjectiveBaseMap (g ≫ f) n = BaseMaps.relativeProjectiveBaseMap g n ≫ BaseMaps.relativeProjectiveBaseMap f n := by
  apply (Projective.AffineCover.projectiveAffineOpenCover U.affineOpenCover n).hom_ext
  intro i
  change AffineProjective.Charts.affineProjectiveChartMap (U.affineOpenCover.f i) n ≫ BaseMaps.relativeProjectiveBaseMap (g ≫ f) n =
    AffineProjective.Charts.affineProjectiveChartMap (U.affineOpenCover.f i) n ≫ (BaseMaps.relativeProjectiveBaseMap g n ≫ BaseMaps.relativeProjectiveBaseMap f n)
  rw [← Category.assoc, BaseMaps.relativeProjectiveBaseMap_affine, BaseMaps.relativeProjectiveBaseMap_affine,
    BaseMaps.relativeProjectiveBaseMap_affine, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseFunctoriality
