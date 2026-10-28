import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ChartNormalizedRankPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartIntersections

/-! # Polynomial Rank Right -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRankRight

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

theorem stableChartIntersection_polynomialRank_right (D q : ℕ) :
    BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) D q ↔
      BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D q := by
  let v := Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ
  have hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (j.exponent + k.exponent)) :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i (j.intersection k) ρ
  have hvprod := hv
  rw [Balanced.MonomialAlgebra.exponentMonomial_add] at hvprod
  have hvk : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) k.exponent) :=
    (IsUnit.mul_iff.mp hvprod).2
  have he : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v (j.exponent + k.exponent)
      ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced) hv = ρ.toRingHom :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R i (j.intersection k) ρ
  have hek : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v k.exponent k.balanced hvk =
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced)).toRingHom := by
    rw [← BalancedChart.IntersectionMaps.balancedConfigurationChartEvaluation_intersection_right R i j.exponent k.exponent
      j.balanced k.balanced v hvk hv, he]
    rfl
  exact Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_rank_iff R i k _ v hvk hek D q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRankRight
