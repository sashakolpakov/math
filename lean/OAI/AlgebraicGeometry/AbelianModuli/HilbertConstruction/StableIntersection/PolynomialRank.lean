import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRankLeft
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRankRight
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartIntersections

/-! # Polynomial Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRank

noncomputable section

/-! On the actual product-denominator chart, the two normalized
coordinate configurations have the same polynomial flat-rank
condition. This comparison holds on every coefficient-algebra point
and uses the actual intersection restriction maps. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A)

theorem stableChartIntersection_polynomialRank_comparisons (D q : ℕ) :
    (BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced))) D q ↔
      BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D q) ∧
    (BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) D q ↔
      BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D q) :=
  ⟨PolynomialRankLeft.stableChartIntersection_polynomialRank_left R i j k ρ D q,
    PolynomialRankRight.stableChartIntersection_polynomialRank_right R i j k ρ D q⟩

theorem stableChartIntersection_polynomialRank_iff (D q : ℕ) :
    BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced))) D q ↔
      BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) D q :=
  (stableChartIntersection_polynomialRank_comparisons R i j k ρ D q).1.trans
    (stableChartIntersection_polynomialRank_comparisons R i j k ρ D q).2.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRank
