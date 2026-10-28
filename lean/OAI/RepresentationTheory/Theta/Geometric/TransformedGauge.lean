import OAI.RepresentationTheory.Theta.Geometric.ExtendedCoordinates
import OAI.RepresentationTheory.Theta.Geometric.PowerGauge

/-! # Transformed Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.TransformedGauge

noncomputable section

/-! Ratios between original and transformed theta coordinates are actual
algebraic units on the enlarged theta embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
  (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.withSectionMap T).projectiveDimension))

def transformedThetaGaugeOpen (i j : Fin (F.projectiveDimension + 1)) : X.left.Opens :=
  f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ)
    (F.withSectionMapOriginalIndex T i) (F.withSectionMapTransformedIndex T j)

def transformedThetaGaugeUnit (i j : Fin (F.projectiveDimension + 1)) :
    Γ(X.left, transformedThetaGaugeOpen F T f i j)ˣ :=
  PowerGauge.projectivePullbackTransitionUnit f.left
    (F.withSectionMapOriginalIndex T i) (F.withSectionMapTransformedIndex T j)

theorem transformedThetaGaugeUnit_value (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.withSectionMap T).projectiveDimension ((F.withSectionMap T).projectiveMap t))
    (i j : Fin (F.projectiveDimension + 1)) (z : Φ.space)
    (hx : (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ transformedThetaGaugeOpen F T f i j) :
    Complex.SectionEvaluation.complexSectionValue (e (QuotientAddGroup.mk z)).left (transformedThetaGaugeOpen F T f i j) hx
      (transformedThetaGaugeUnit F T f i j : Γ(X.left, transformedThetaGaugeOpen F T f i j)) =
      T (F.coordinate j) z / F.coordinate i z := by
  have h := PowerGauge.projectivePullbackTransitionUnit_value f (e (QuotientAddGroup.mk z))
    ((F.withSectionMap T).projectiveMap (QuotientAddGroup.mk z)) (he (QuotientAddGroup.mk z))
    (F.withSectionMapOriginalIndex T i) (F.withSectionMapTransformedIndex T j) hx
  rw [(F.withSectionMap T).projectiveMap_coordinates] at h
  change _ = (F.withSectionMap T).coordinate (F.withSectionMapTransformedIndex T j) z /
    (F.withSectionMap T).coordinate (F.withSectionMapOriginalIndex T i) z at h
  exact h.trans (by rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapOriginalIndex_coordinate, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapTransformedIndex_coordinate])

end

end OAI.RepresentationTheory.Theta.Geometric.TransformedGauge
