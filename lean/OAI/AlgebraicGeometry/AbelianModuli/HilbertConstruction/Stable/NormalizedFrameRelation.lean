import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.PolynomialRank

/-! # Normalized Frame Relation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual normalized configurations on a stable chart
intersection are related by a uniquely determined projective
coordinate isomorphism over its coefficient spectrum. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem Configuration.ProjectiveTransport.ConfigurationFrameRelated.symm {R : Type u} [CommRing R] {n : ℕ} {ι : Type v}
    {v w : ι → Fin (n + 1) → R} (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w) : Configuration.ProjectiveTransport.ConfigurationFrameRelated w v := by
  obtain ⟨T, s, h⟩ := h
  refine ⟨T.symm, fun z => (s z)⁻¹, fun z => ?_⟩
  rw [h z, T.symm.map_smul, T.symm_apply_apply, ← mul_smul, Units.inv_mul, one_smul]

theorem Configuration.ProjectiveTransport.ConfigurationFrameRelated.trans {R : Type u} [CommRing R] {n : ℕ} {ι : Type v}
    {v w z : ι → Fin (n + 1) → R} (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w) (h' : Configuration.ProjectiveTransport.ConfigurationFrameRelated w z) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated v z := by
  obtain ⟨T, s, h⟩ := h
  obtain ⟨U, t, h'⟩ := h'
  refine ⟨T.trans U, fun a => t a * s a, fun a => ?_⟩
  rw [h' a, h a, U.map_smul, smul_smul, Units.val_mul]
  rfl

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

theorem Stable.NormalizedFrameRelation.stableChartNormalizedPoint_hasFrame
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A) :
    IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun A (Fin (n + 1)))
      (fun a => Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j ρ (j.frame a))
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j ρ j.additional)) := by
  rw [← Frame.ChartDenominators.frameDiscriminantExponent_monomial]
  exact Unit.MonomialFractions.exponentMonomial_isUnit_of_le _ ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le) (Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i j ρ)

theorem Stable.NormalizedFrameRelation.stableChartNormalizedPoint_frameRelated
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A)
    (v : Fin m → Fin (n + 1) → A)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))
    (heval : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hv = ρ.toRingHom) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated v (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j ρ) :=
  BalancedChart.FiberOrbits.balancedChart_equal_evaluation_implies_same_orbit i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le) v (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j ρ)
    hv (Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i j ρ)
    (heval.trans (Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R i j ρ).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
