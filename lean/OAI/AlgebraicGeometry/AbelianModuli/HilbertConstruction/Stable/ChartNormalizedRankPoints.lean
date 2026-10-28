import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.PolynomialRankInvariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex

/-! # Chart Normalized Rank Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ChartNormalizedRankPoints

noncomputable section

/-! An algebra-valued stable chart point has a specified normalized
configuration: apply the algebra map to the universal chart vectors.
Its polynomial rank condition agrees with that of every configuration
giving the same chart evaluation map. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

def stableChartNormalizedPointVectors
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A) : Fin m → Fin (n + 1) → A :=
  fun z k => ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete z k)

theorem stableChartNormalizedPoint_denominatorUnit
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (stableChartNormalizedPointVectors R i j ρ))
      j.exponent) := by
  let v := Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete
  have hu := Normalized.BalancedDenominatorUnit.normalizedBalancedDenominator_isUnit R (Nat.succ_pos n) i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le)
  have he : ρ (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent) =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (stableChartNormalizedPointVectors R i j ρ)) j.exponent := by
    change ρ.toRingHom (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent) = _
    rw [MonomialExponentExtension.exponentMonomial_map]
    congr 1
    funext τ
    exact LabeledDeterminantPolynomials.labeledDeterminant_map ρ.toRingHom τ v
  exact he ▸ hu.map ρ.toRingHom

def stableChartNormalizedPointConfiguration
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A) : BalancedChart.ConfigurationOrbits.BalancedChartConfiguration A j.exponent :=
  ⟨stableChartNormalizedPointVectors R i j ρ, stableChartNormalizedPoint_denominatorUnit R i j ρ⟩

theorem stableChartNormalizedPoint_evaluation
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A) :
    Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i (stableChartNormalizedPointVectors R i j ρ)
      j.exponent j.balanced (stableChartNormalizedPoint_denominatorUnit R i j ρ) = ρ.toRingHom := by
  let v := Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete
  have hu := Normalized.BalancedDenominatorUnit.normalizedBalancedDenominator_isUnit R (Nat.succ_pos n) i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le)
  have hid : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hu = RingHom.id _ :=
    Normalized.BalancedChartIdentity.normalizedBalancedChartEndomorphism_eq_id R (Nat.succ_pos n) i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le)
  have h := BalancedChart.EvaluationNaturality.balancedConfigurationChartEvaluation_comp i v j.exponent j.balanced hu ρ
    (stableChartNormalizedPoint_denominatorUnit R i j ρ)
  rw [hid, RingHom.comp_id] at h
  exact h.symm

theorem stableChartNormalizedPoint_rank_iff
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A)
    (v : Fin m → Fin (n + 1) → A)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))
    (heval : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hv = ρ.toRingHom)
    (D k : ℕ) :
    BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank (stableChartNormalizedPointVectors R i j ρ) D k ↔
      BalancedChart.PolynomialRankInvariance.ConfigurationPolynomialFlatRank v D k :=
  BalancedChart.PolynomialRankInvariance.balancedChart_equal_evaluation_polynomialFlatRank i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le) v (stableChartNormalizedPointVectors R i j ρ)
    hv (stableChartNormalizedPoint_denominatorUnit R i j ρ)
    (heval.trans (stableChartNormalizedPoint_evaluation R i j ρ).symm) D k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ChartNormalizedRankPoints
