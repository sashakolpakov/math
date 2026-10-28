import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.RelationsLeft
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.RelationsRight
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartIntersections

/-! # Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.Relations

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

theorem stableChartIntersection_hilbertRelations_comparisons (D : ℕ) (P : Polynomial ℚ) :
    (Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced))) D P ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D P) ∧
    (Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) D P ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i (j.intersection k) ρ) D P) :=
  ⟨RelationsLeft.stableChartIntersection_hilbertRelations_left R i j k ρ D P,
    RelationsRight.stableChartIntersection_hilbertRelations_right R i j k ρ D P⟩

theorem stableChartIntersection_hilbertRelations_iff (D : ℕ) (P : Polynomial ℚ) :
    Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced))) D P ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) D P :=
  (stableChartIntersection_hilbertRelations_comparisons R i j k ρ D P).1.trans
    (stableChartIntersection_hilbertRelations_comparisons R i j k ρ D P).2.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.Relations
