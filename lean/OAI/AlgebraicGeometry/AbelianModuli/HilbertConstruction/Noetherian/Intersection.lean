import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IntersectionBaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.AffineCoverLifts

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.Intersection

noncomputable section

/-! The Hilbert conditions agree on actual stable rank
intersections for every locally Noetherian test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (T : Over (Spec (.of R))) [IsLocallyNoetherian T.left]
variable (y : T ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i (j.intersection k) D (Stable.ConfigurationLocus.configurationHilbertRank D P))

include hP hD

theorem noetherianHilbertIntersection_left_iff :
    (∃! a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P =
        y ≫ Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)) ↔
    (∃! a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P = y) := by
  rw [HilbertConstruction.Over.AffineCoverLifts.overUniqueLift_iff_affineOpenCover, HilbertConstruction.Over.AffineCoverLifts.overUniqueLift_iff_affineOpenCover]
  apply forall_congr'
  intro a
  have : IsNoetherianRing (T.left.affineOpenCover.X a) := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (T.left.affineOpenCover.f a))
  simpa only [Category.assoc] using Affine.IntersectionBaseMaps.affineHilbertIntersection_left_iff R (T.left.affineOpenCover.X a)
    i j k D P hP hD (T.left.affineOpenCover.f a ≫ T.hom) (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a ≫ y)

theorem noetherianHilbertIntersection_right_iff :
    (∃! a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P =
        y ≫ Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)) ↔
    (∃! a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P = y) := by
  rw [HilbertConstruction.Over.AffineCoverLifts.overUniqueLift_iff_affineOpenCover, HilbertConstruction.Over.AffineCoverLifts.overUniqueLift_iff_affineOpenCover]
  apply forall_congr'
  intro a
  have : IsNoetherianRing (T.left.affineOpenCover.X a) := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (T.left.affineOpenCover.f a))
  simpa only [Category.assoc] using Affine.IntersectionBaseMaps.affineHilbertIntersection_right_iff R (T.left.affineOpenCover.X a)
    i j k D P hP hD (T.left.affineOpenCover.f a ≫ T.hom) (HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a ≫ y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.Intersection
