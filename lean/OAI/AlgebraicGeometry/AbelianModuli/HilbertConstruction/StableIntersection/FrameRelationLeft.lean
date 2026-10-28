import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.NormalizedFrameRelation

/-! # Frame Relation Left -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.FrameRelationLeft

noncomputable section

/-! One normalized frame comparison on a stable chart intersection. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
theorem stableChartIntersection_LeftFrameRelated
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ)
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced))) := by
  let v := Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ
  have hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (j.exponent + k.exponent)) :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i (j.intersection k) ρ
  have hprod := hv
  rw [Balanced.MonomialAlgebra.exponentMonomial_add] at hprod
  have hvj := (IsUnit.mul_iff.mp hprod).1
  have he : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v (j.exponent + k.exponent)
      ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced) hv = ρ.toRingHom :=
    Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R i (j.intersection k) ρ
  have hj : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hvj =
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)).toRingHom := by
    rw [← BalancedChart.IntersectionMaps.balancedConfigurationChartEvaluation_intersection_left R i j.exponent k.exponent
      j.balanced k.balanced v hvj hv, he]
    rfl
  exact Stable.NormalizedFrameRelation.stableChartNormalizedPoint_frameRelated R i j _ v hvj hj

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.FrameRelationLeft
