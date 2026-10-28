import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.Relations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartIntersections

/-! # Relations Left -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.RelationsLeft

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

theorem stableChartIntersection_hilbertRelations_left (D : ℕ) (P : Polynomial ℚ) :
    Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced))) D P ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D P := by
  let v := Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ
  have hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (j.exponent + k.exponent)) :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i (j.intersection k) ρ
  have hvprod := hv
  rw [Balanced.MonomialAlgebra.exponentMonomial_add] at hvprod
  have hvj : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent) :=
    (IsUnit.mul_iff.mp hvprod).1
  have he : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v (j.exponent + k.exponent)
      ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced) hv = ρ.toRingHom :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R i (j.intersection k) ρ
  have hej : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hvj =
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)).toRingHom := by
    rw [← BalancedChart.IntersectionMaps.balancedConfigurationChartEvaluation_intersection_left R i j.exponent k.exponent
      j.balanced k.balanced v hvj hv, he]
    rfl
  exact BalancedChart.Relations.stableChartNormalizedPoint_hilbertRelations_iff (R := R) i j _ v hvj hej D P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.RelationsLeft
