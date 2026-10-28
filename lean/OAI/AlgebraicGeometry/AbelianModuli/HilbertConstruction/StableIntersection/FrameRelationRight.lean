import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.NormalizedFrameRelation

/-! # Frame Relation Right -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.FrameRelationRight

noncomputable section

/-! One normalized frame comparison on a stable chart intersection. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
theorem stableChartIntersection_RightFrameRelated
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ)
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) := by
  let v := Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ
  have hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (j.exponent + k.exponent)) :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i (j.intersection k) ρ
  have hprod := hv
  rw [Balanced.MonomialAlgebra.exponentMonomial_add] at hprod
  have hvk := (IsUnit.mul_iff.mp hprod).2
  have he : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v (j.exponent + k.exponent)
      ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced) hv = ρ.toRingHom :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R i (j.intersection k) ρ
  have hk : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v k.exponent k.balanced hvk =
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced)).toRingHom := by
    rw [← BalancedChart.IntersectionMaps.balancedConfigurationChartEvaluation_intersection_right R i j.exponent k.exponent
      j.balanced k.balanced v hvk hv, he]
    rfl
  exact Stable.NormalizedFrameRelation.stableChartNormalizedPoint_frameRelated R i k _ v hvk hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.FrameRelationRight
