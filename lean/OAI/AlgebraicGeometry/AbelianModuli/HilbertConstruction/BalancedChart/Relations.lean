import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.RelationInvariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ChartNormalizedRankPoints

/-! # Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.Relations

noncomputable section

/-! The Hilbert relation condition is independent of the chosen
configuration representative of a balanced chart algebra point. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
variable {n m : ℕ}

local instance balancedChartRingCommRing
    (i : Fin m) (a : (Fin (n + 1) → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) :
    CommRing (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha) := inferInstance

theorem balancedChart_equal_evaluation_hilbertRelations
    (i : Fin m) (σ : Fin (n + 1) → Fin m) (e : Fin m) (c : Fin m → Fin (n + 1))
    (a : (Fin (n + 1) → Fin m) → ℕ) (C : Fin m → (Fin (n + 1) → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (v w : Fin m → Fin (n + 1) → A)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a))
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a))
    (heval : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v a ha hv =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw) (D : ℕ) (P : Polynomial ℚ) :
    Configuration.RelationInvariance.ConfigurationHasHilbertRelations w D P ↔ Configuration.RelationInvariance.ConfigurationHasHilbertRelations v D P := by
  obtain ⟨T, s, hs⟩ := FiberOrbits.balancedChart_equal_evaluation_implies_same_orbit
    i σ e c a C ha hC hframe v w hv hw heval
  exact Configuration.RelationInvariance.configurationHasHilbertRelations_frameOrbit_iff v w T s hs D P

theorem stableChartNormalizedPoint_hilbertRelations_iff
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] A)
    (v : Fin m → Fin (n + 1) → A)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))
    (heval : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hv = ρ.toRingHom)
    (D : ℕ) (P : Polynomial ℚ) :
    Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j ρ) D P ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations v D P :=
  balancedChart_equal_evaluation_hilbertRelations i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le) v (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j ρ)
    hv (Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R i j ρ)
    (heval.trans (Stable.ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R i j ρ).symm) D P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.Relations
