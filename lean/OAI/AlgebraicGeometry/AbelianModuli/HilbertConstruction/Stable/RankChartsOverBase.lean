import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverPullbackReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankIntersectionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase

/-! # Rank Charts Over Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartsOverBase

noncomputable section

/-! The stable affine chart maps and their polynomial rank loci
retain the coefficient-spectrum structure map. Their intersection
maps commute as morphisms over that original base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

theorem stableBalancedAffineChartMap_over :
    BalancedAffineCover.stableBalancedAffineChartMap R i j ≫ (BalancedProjectiveOpen.stableBalancedQuotientScheme (r := n + 1) R i).hom =
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j).hom := by
  change BalancedAffineCover.stableBalancedAffineChartMap R i j ≫
    ((BalancedProjectiveOpen.stableBalancedProjectiveOpen R i).ι ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Balanced.DeterminantGrading.balancedDeterminantGrading R (n + 1) m i)) = _
  rw [← Category.assoc, BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion, Projective.MapOverBase.projectiveStructureMap_positiveAway]
  rfl

def stableBalancedAffineChartOverMap :
    ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j ⟶ BalancedProjectiveOpen.stableBalancedQuotientScheme (r := n + 1) R i :=
  Over.homMk (BalancedAffineCover.stableBalancedAffineChartMap R i j) (stableBalancedAffineChartMap_over R i j)

theorem stableChartIntersectionLeftOver_factor :
    StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k ≫ stableBalancedAffineChartOverMap R i j =
      stableBalancedAffineChartOverMap R i (j.intersection k) :=
  Over.OverMorphism.ext (BalancedChartOverlapMorphisms.stableBalancedAffineChartMap_intersection_left R i j k)

theorem stableChartIntersectionRightOver_factor :
    StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k ≫ stableBalancedAffineChartOverMap R i k =
      stableBalancedAffineChartOverMap R i (j.intersection k) :=
  Over.OverMorphism.ext (BalancedChartOverlapMorphisms.stableBalancedAffineChartMap_intersection_right R i j k)

private theorem nativeIntersectionLeftMap :
    (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k).left =
      Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionLeft R i j.exponent k.exponent j.balanced k.balanced)) := rfl

private theorem nativeIntersectionRightMap :
    (StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k).left =
      Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionRight R i j.exponent k.exponent j.balanced k.balanced)) := rfl

private theorem nativeAffineChartMapLeft (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n+1) m) :
    (stableBalancedAffineChartOverMap R i j).left = BalancedAffineCover.stableBalancedAffineChartMap R i j := rfl

private theorem nativeChartIntersectionLeftPullback :
    IsPullback (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k).left (StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k).left
      (stableBalancedAffineChartOverMap R i j).left (stableBalancedAffineChartOverMap R i k).left := by
  rw [nativeIntersectionLeftMap, nativeIntersectionRightMap, nativeAffineChartMapLeft, nativeAffineChartMapLeft]
  exact BalancedChartPullbacks.stableBalancedChartIntersection_isPullback R i j k

theorem stableChartIntersectionOver_isPullback :
    IsPullback (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) (StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k)
      (stableBalancedAffineChartOverMap R i j) (stableBalancedAffineChartOverMap R i k) :=
  HilbertScheme.Presentations.OverPullbackReflection.overPullbackOfLeft _ _ _ _ (nativeChartIntersectionLeftPullback R i j k)

def stableRankChartToStable (D q : ℕ) :
    ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q ⟶ BalancedProjectiveOpen.stableBalancedQuotientScheme (r := n + 1) R i :=
  ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q ≫ stableBalancedAffineChartOverMap R i j

theorem stableRankIntersectionLeftMap_toStable (D q : ℕ) :
    RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D q ≫ stableRankChartToStable R i j D q =
      stableRankChartToStable R i (j.intersection k) D q := by
  rw [stableRankChartToStable, ← Category.assoc, RankIntersectionMaps.stableRankIntersectionLeftMap_factor,
    Category.assoc, stableChartIntersectionLeftOver_factor]
  rfl

theorem stableRankIntersectionRightMap_toStable (D q : ℕ) :
    RankIntersectionMaps.stableRankIntersectionRightMap R i j k D q ≫ stableRankChartToStable R i k D q =
      stableRankChartToStable R i (j.intersection k) D q := by
  rw [stableRankChartToStable, ← Category.assoc, RankIntersectionMaps.stableRankIntersectionRightMap_factor,
    Category.assoc, stableChartIntersectionRightOver_factor]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartsOverBase
