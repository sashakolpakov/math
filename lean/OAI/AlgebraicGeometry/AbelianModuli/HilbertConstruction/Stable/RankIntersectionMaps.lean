import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.SchemeRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankLocusTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartPullbacks

/-! # Rank Intersection Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankIntersectionMaps

noncomputable section

/-! Actual product-denominator rank loci map to both stable chart
rank loci. These maps are open immersions and their squares with
the ambient intersection maps are Cartesian. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D q : ℕ)

def stableRankIntersectionLeftMap :
    ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i (j.intersection k) D q ⟶
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q :=
  Matrix.RankLocusTransport.matrixRankLocusTransport
    (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))
    (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i (j.intersection k) D)
    (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) (fun T x => StableIntersection.SchemeRank.stableIntersectionPolynomialRank_left_iff R i j k T x D q)

def stableRankIntersectionRightMap :
    ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i (j.intersection k) D q ⟶
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i k D q :=
  Matrix.RankLocusTransport.matrixRankLocusTransport
    (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i k) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k))
    (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i k D) (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i (j.intersection k) D)
    (StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k) (fun T x => StableIntersection.SchemeRank.stableIntersectionPolynomialRank_right_iff R i j k T x D q)

theorem stableRankIntersectionLeftMap_factor :
    stableRankIntersectionLeftMap R i j k D q ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q =
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D q ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k :=
  Matrix.RankLocusTransport.matrixRankLocusTransport_factor _ _ _ _ _ _

theorem stableRankIntersectionRightMap_factor :
    stableRankIntersectionRightMap R i j k D q ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D q =
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D q ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k :=
  Matrix.RankLocusTransport.matrixRankLocusTransport_factor _ _ _ _ _ _

theorem stableRankIntersectionLeft_isPullback :
    IsPullback (stableRankIntersectionLeftMap R i j k D q).left
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D q).left
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D q).left (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k).left :=
  Matrix.RankLocusTransport.matrixRankLocusTransport_isPullback_left _ _ _ _ _ _

theorem stableRankIntersectionRight_isPullback :
    IsPullback (stableRankIntersectionRightMap R i j k D q).left
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i (j.intersection k) D q).left
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D q).left (StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k).left :=
  Matrix.RankLocusTransport.matrixRankLocusTransport_isPullback_left _ _ _ _ _ _

instance stableChartIntersectionLeftOver_open : IsOpenImmersion (StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (BalancedChartPullbacks.stableBalancedChartIntersection_isPullback R i j k).flip inferInstance

instance stableChartIntersectionRightOver_open : IsOpenImmersion (StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (BalancedChartPullbacks.stableBalancedChartIntersection_isPullback R i j k) inferInstance

instance stableRankIntersectionLeftMap_open : IsOpenImmersion (stableRankIntersectionLeftMap R i j k D q).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (stableRankIntersectionLeft_isPullback R i j k D q).flip inferInstance

instance stableRankIntersectionRightMap_open : IsOpenImmersion (stableRankIntersectionRightMap R i j k D q).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (stableRankIntersectionRight_isPullback R i j k D q).flip inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankIntersectionMaps
