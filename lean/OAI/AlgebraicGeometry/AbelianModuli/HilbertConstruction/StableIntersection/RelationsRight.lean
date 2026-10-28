import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.Relations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartIntersections

/-! # Relations Right -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.RelationsRight

noncomputable section

/-! The actual stable chart intersection preserves existence of a saturated
flat Hilbert ideal with the prescribed polynomial relation kernel,
on every Noetherian coefficient-algebra point. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [IsNoetherianRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A)

theorem stableChartIntersection_hilbertRelations_right (D : ℕ) (P : Polynomial ℚ) :
    Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) D P ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D P := by
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
  exact BalancedChart.Relations.stableChartNormalizedPoint_hilbertRelations_iff (R := R) i k _ v hvk hek D P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.RelationsRight
