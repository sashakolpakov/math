import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedOrbitEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange

/-! # Balanced Projective Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectivePoints.StableHilbertCoverage

noncomputable section

/-! The normalized vector coordinates of an arbitrary stable-chart
point define exactly the pullbacks of its original projective marks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (T : Over (Spec (.of R)))
variable (a : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)

theorem normalizedVectors_coordinate (z : Fin m) (k : Fin (n + 1)) :
    BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T a z k =
      a.left.appTop ((Scheme.ΓSpecIso
        (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv
          (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
            j.exponent j.complement j.balanced j.complete z k)) := rfl

theorem normalizedVectors_cover (z : Fin m) :
    ∀ x : T.left, ∃ k, x ∈ T.left.basicOpen (BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T a z k) :=
  Balanced.FrameChartProjectivePoints.balancedFrameChartProjectiveCoordinates_cover R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete T.left
    (a.left.appTop.hom.comp
      (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom) z

theorem normalizedProjectivePoint_baseChange (z : Fin m) :
    Projective.SectionBaseChange.projectiveSectionBaseChange
      (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
        j.exponent j.complement j.balanced j.complete z) a.left =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T a z)
        (normalizedVectors_cover R i j T a z) :=
  Balanced.FramePointBaseChange.balancedFrameChartUniversalPoint_baseChange R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete a.left z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectivePoints.StableHilbertCoverage
