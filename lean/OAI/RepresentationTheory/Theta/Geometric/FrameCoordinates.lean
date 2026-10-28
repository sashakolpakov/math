import OAI.RepresentationTheory.Theta.Geometric.Projective.SectionEvaluation
import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies

/-! # Frame Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.FrameCoordinates

noncomputable section

/-! The actual algebraic hyperplane coordinates pull back to theta ratios. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projective_pullback_localEquation_value {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {n : ℕ}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (he : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p)
    (i k : Fin (n + 1)) (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p)
    (hx : x.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    Complex.SectionEvaluation.complexSectionValue x.left (f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) hx
      (f.left.app (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
        (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k)) =
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p k := by
  have hpoint : x.left ≫ f.left = (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left :=
    congrArg (fun t : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n => t.left) he
  have h := Complex.SectionEvaluation.complexSectionValue_pullback x.left f.left (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl hx
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k)
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h.trans ((Complex.SectionEvaluation.complexSectionValue_congr _ _ hpoint _ _
    ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i p).mpr hi) _).trans
    (Projective.SectionEvaluation.projective_localEquation_value n i k p hi))

theorem theta_pullback_localEquation_value {Φ : Torus.Data.CM.ProjectivePeriodData}
    {J : Φ.AutomorphyFactor} (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (z : Φ.space) (i k : Fin (F.projectiveDimension + 1)) (hi : F.coordinate i z ≠ 0)
    (hx : (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i) :
    Complex.SectionEvaluation.complexSectionValue (e (QuotientAddGroup.mk z)).left
      (f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i) hx
      (f.left.app (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i)
        (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k)) =
      F.coordinate k z / F.coordinate i z := by
  have h := projective_pullback_localEquation_value f (e (QuotientAddGroup.mk z))
    (F.projectiveMap (QuotientAddGroup.mk z)) (he (QuotientAddGroup.mk z)) i k
    ((F.projectiveMap_inPatch i z).mpr hi) hx
  rw [F.projectiveMap_coordinates] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.FrameCoordinates
