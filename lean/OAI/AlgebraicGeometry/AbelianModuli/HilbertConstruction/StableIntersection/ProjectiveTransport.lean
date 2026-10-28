import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.FrameRelationLeft
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.FrameRelationRight

/-! # Projective Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.ProjectiveTransport

noncomputable section

/-! Compose the two cached normalized frame comparisons into their projective isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
theorem stableChartIntersection_frameRelated
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)))
      (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced))) :=
  (FrameRelationLeft.stableChartIntersection_LeftFrameRelated R i j k ρ).symm.trans
    (FrameRelationRight.stableChartIntersection_RightFrameRelated R i j k ρ)

def stableChartIntersectionProjectiveIso
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.intersection k).exponent (j.intersection k).balanced →ₐ[R] A) :
    Projective.ProjectivePresentations.affineProjectiveSpace A n ≅ Projective.ProjectivePresentations.affineProjectiveSpace A n :=
  Configuration.ProjectiveTransport.configurationProjectiveTransport
    (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)))
    (Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
      (ρ.comp (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced)))
    (stableChartIntersection_frameRelated R i j k ρ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.ProjectiveTransport
