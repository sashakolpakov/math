import OAI.RepresentationTheory.Theta.Geometric.CommonPower
import OAI.RepresentationTheory.Theta.Geometric.FrameCoordinates

/-! # Power Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerGauge

noncomputable section

/-! The mixed ratios of theta coordinate powers are actual algebraic units
on the overlap of the corresponding opens in the common projective model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def projectivePullbackTransitionUnit {X : Scheme} {n : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (i k : Fin (n + 1)) :
    Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)ˣ :=
  Units.map (f.app (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)).hom.toMonoidHom
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k)

theorem projectivePullbackTransitionUnit_value {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {n : ℕ}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (he : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p)
    (i k : Fin (n + 1))
    (hx : x.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    Complex.SectionEvaluation.complexSectionValue x.left (f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) hx
      (projectivePullbackTransitionUnit f.left i k :
        Γ(X.left, f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) =
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p k := by
  have hpoint : x.left ≫ f.left = (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left :=
    congrArg (fun t : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n => t.left) he
  have hp : (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k := by
    rw [← hpoint]
    exact hx
  have h := Complex.SectionEvaluation.complexSectionValue_pullback x.left f.left
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) le_rfl hx
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k :
      Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k))
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h.trans ((Complex.SectionEvaluation.complexSectionValue_congr _ _ hpoint _ _ hp _).trans
    (Projective.SectionEvaluation.projective_transitionUnit_value n i k p hp))

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
  (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonPower G).projectiveDimension))

def thetaPowerGaugeOpen (i : Fin (F.projectiveDimension + 1))
    (j : Fin (G.projectiveDimension + 1)) : X.left.Opens :=
  f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ)
    (F.commonPowerLeftIndex G i) (F.commonPowerRightIndex G j)

def thetaPowerGaugeUnit (i : Fin (F.projectiveDimension + 1))
    (j : Fin (G.projectiveDimension + 1)) : Γ(X.left, thetaPowerGaugeOpen F G f i j)ˣ :=
  projectivePullbackTransitionUnit f.left (F.commonPowerLeftIndex G i) (F.commonPowerRightIndex G j)

theorem thetaPowerGaugeUnit_value (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonPower G).projectiveDimension ((F.commonPower G).projectiveMap t))
    (i : Fin (F.projectiveDimension + 1)) (j : Fin (G.projectiveDimension + 1)) (z : Φ.space)
    (hx : (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ thetaPowerGaugeOpen F G f i j) :
    Complex.SectionEvaluation.complexSectionValue (e (QuotientAddGroup.mk z)).left (thetaPowerGaugeOpen F G f i j) hx
      (thetaPowerGaugeUnit F G f i j : Γ(X.left, thetaPowerGaugeOpen F G f i j)) =
      G.coordinate j z ^ F.degree / F.coordinate i z ^ G.degree := by
  have h := projectivePullbackTransitionUnit_value f (e (QuotientAddGroup.mk z))
    ((F.commonPower G).projectiveMap (QuotientAddGroup.mk z)) (he (QuotientAddGroup.mk z))
    (F.commonPowerLeftIndex G i) (F.commonPowerRightIndex G j) hx
  rw [(F.commonPower G).projectiveMap_coordinates] at h
  change _ = (F.commonPower G).coordinate (F.commonPowerRightIndex G j) z /
    (F.commonPower G).coordinate (F.commonPowerLeftIndex G i) z at h
  exact h.trans (by rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerLeftIndex_coordinate, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerRightIndex_coordinate])

end

end OAI.RepresentationTheory.Theta.Geometric.PowerGauge
