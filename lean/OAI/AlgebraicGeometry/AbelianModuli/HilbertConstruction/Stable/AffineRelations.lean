import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineAlgebraPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.KernelCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.Relations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.SchemeRank

/-! # Affine Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.AffineRelations

noncomputable section

/-! A stable affine chart point has literal normalized algebra
coordinates. In those coordinates its Hilbert-lift criterion is
the invariant homogeneous relation condition. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineAlgebraPoints
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {C : Type u} [CommRing C] [Algebra R C]
variable {n m : ℕ} (i : Fin m) (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

abbrev stableChartAffineAlgebraPoint
    (x : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →ₐ[R] C :=
  HilbertScheme.Presentations.Relative.AffineAlgebraPoints.relativeAffineAlgebraPoint (.of R) C
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) x

theorem stableChartAffineAlgebraPoint_vectors
    (x : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x =
      fun c : ULift.{u} (Fin m) => ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (stableChartAffineAlgebraPoint R i j x) c.down := rfl

abbrev stableChartAffineAlgebraPoint_intersection_left
    (x : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k)) :=
  HilbertScheme.Presentations.Relative.AffineAlgebraPoints.relativeAffineAlgebraPoint_postcomp (.of R) C
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced)
    (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced) x

abbrev stableChartAffineAlgebraPoint_intersection_right
    (x : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k)) :=
  HilbertScheme.Presentations.Relative.AffineAlgebraPoints.relativeAffineAlgebraPoint_postcomp (.of R) C
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i k.exponent k.balanced)
    (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced) x

theorem stableAffineHilbertLift_iff_relations [IsNoetherianRing R] [IsNoetherianRing C]
    (D : ℕ) (P : Polynomial ℚ)
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (x : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (y : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (ConfigurationLocus.configurationHilbertRank D P))
    (hy : y ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (ConfigurationLocus.configurationHilbertRank D P) = x) :
    (∃! a : HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C ⟶ ConfigurationLocus.stableConfigurationHilbertLocus R i j D P,
      a ≫ ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P = y) ↔
      Configuration.RelationInvariance.ConfigurationHasHilbertRelations (ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (stableChartAffineAlgebraPoint R i j x)) D P := by
  refine (StableHilbert.KernelCriterion.stableConfigurationHilbertLift_iff_kernelIdeal R (.of C) i j D P hP hD x y hy).trans ?_
  rw [← Configuration.RelationInvariance.configurationHasHilbertRelations_matrix_iff, stableChartAffineAlgebraPoint_vectors]
  exact Configuration.RelationInvariance.configurationHasHilbertRelations_relabel_iff _ Equiv.ulift D P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.AffineRelations
