import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.AffineRelations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankIntersectionMaps

/-! # Affine Intersection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.AffineIntersection

noncomputable section

/-! On each actual rank-chart intersection, the two Hilbert
lifting conditions coincide on every Noetherian algebra-valued
affine test. Both agree with the intersection's own Hilbert locus. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra R C]
variable {n m : ℕ} (i : Fin m) (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (y : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶
  ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i (j.intersection k) D (ConfigurationLocus.configurationHilbertRank D P))

include hP hD

theorem stableAffineHilbertIntersection_left_iff :
    (∃! a : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationLocus.stableConfigurationHilbertLocus R i j D P,
      a ≫ ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P =
        y ≫ RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (ConfigurationLocus.configurationHilbertRank D P)) ↔
    (∃! a : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P,
      a ≫ ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P = y) := by
  let x := y ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D (ConfigurationLocus.configurationHilbertRank D P)
  have hy : (y ≫ RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (ConfigurationLocus.configurationHilbertRank D P)) ≫
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (ConfigurationLocus.configurationHilbertRank D P) =
        x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k := by
    simpa only [x, Category.assoc] using congrArg (fun a => y ≫ a)
      (RankIntersectionMaps.stableRankIntersectionLeftMap_factor R i j k D (ConfigurationLocus.configurationHilbertRank D P))
  rw [AffineRelations.stableAffineHilbertLift_iff_relations R i j D P hP hD _ _ hy,
    AffineRelations.stableAffineHilbertLift_iff_relations R i (j.intersection k) D P hP hD x y rfl,
]
  simp only [AffineRelations.stableChartAffineAlgebraPoint, StableIntersection.SchemeRank.stableChartIntersectionLeftOver]
  rw [AffineRelations.stableChartAffineAlgebraPoint_intersection_left]
  exact (StableIntersection.Relations.stableChartIntersection_hilbertRelations_comparisons R i j k
    (AffineRelations.stableChartAffineAlgebraPoint R i (j.intersection k) x) D P).1

theorem stableAffineHilbertIntersection_right_iff :
    (∃! a : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationLocus.stableConfigurationHilbertLocus R i k D P,
      a ≫ ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P =
        y ≫ RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (ConfigurationLocus.configurationHilbertRank D P)) ↔
    (∃! a : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P,
      a ≫ ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P = y) := by
  let x := y ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D (ConfigurationLocus.configurationHilbertRank D P)
  have hy : (y ≫ RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (ConfigurationLocus.configurationHilbertRank D P)) ≫
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D (ConfigurationLocus.configurationHilbertRank D P) =
        x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k := by
    simpa only [x, Category.assoc] using congrArg (fun a => y ≫ a)
      (RankIntersectionMaps.stableRankIntersectionRightMap_factor R i j k D (ConfigurationLocus.configurationHilbertRank D P))
  rw [AffineRelations.stableAffineHilbertLift_iff_relations R i k D P hP hD _ _ hy,
    AffineRelations.stableAffineHilbertLift_iff_relations R i (j.intersection k) D P hP hD x y rfl,
]
  simp only [AffineRelations.stableChartAffineAlgebraPoint, StableIntersection.SchemeRank.stableChartIntersectionRightOver]
  rw [AffineRelations.stableChartAffineAlgebraPoint_intersection_right]
  exact (StableIntersection.Relations.stableChartIntersection_hilbertRelations_comparisons R i j k
    (AffineRelations.stableChartAffineAlgebraPoint R i (j.intersection k) x) D P).2

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.AffineIntersection
