import OAI.RepresentationTheory.Theta.Geometric.ProductFrames
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Product Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductValues

noncomputable section

/-! Pointwise values of the native product transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem thetaCoordinateOpen_mem_of_point (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (hp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z))) (i : Fin (F.projectiveDimension + 1)) :
    p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ↔
      F.coordinate i z ≠ 0 := by
  change (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ↔ _
  rw [hp]
  exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen F.projectiveDimension i
    (F.projectiveMap (QuotientAddGroup.mk z))).trans (F.projectiveMap_inPatch i z)

theorem thetaTransitionUnit_value_of_point (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (hp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z))) (i k : Fin (F.projectiveDimension + 1))
    (hx : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    Complex.SectionEvaluation.complexSectionValue p.left _ hx (PowerGauge.projectivePullbackTransitionUnit f.left i k : Γ(X.left, _)) =
      F.coordinate k z / F.coordinate i z := by
  have H := PowerGauge.projectivePullbackTransitionUnit_value f p
    (F.projectiveMap (QuotientAddGroup.mk z)) hp i k hx
  rw [F.projectiveMap_coordinates] at H
  exact H

theorem thetaProductTransitionUnit_value (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) {r : ℕ}
    (f : Fin (r + 1) → (X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension)))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Fin (r + 1) → Φ.space)
    (hp : ∀ k, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f k) p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk (z k))))
    (i j : Fin (r + 1) → Fin (F.projectiveDimension + 1)) (W : X.left.Opens)
    (hW : ∀ k, W ≤ (f k).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (i k) (j k))
    (hx : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    Complex.SectionEvaluation.complexSectionValue p.left W hx
      (ProductFrames.thetaProductTransitionUnit (fun k => (f k).left) i j W hW : Γ(X.left, W)) =
      (∏ k, F.coordinate (j k) (z k)) / (∏ k, F.coordinate (i k) (z k)) := by
  simp only [ProductFrames.thetaProductTransitionUnit, Units.coe_prod, map_prod, PowerGaugeCover.restrictRegularUnit_value]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  exact thetaTransitionUnit_value_of_point F (f k) p (z k) (hp k) (i k) (j k) (hW k hx)

end

end OAI.RepresentationTheory.Theta.Geometric.ProductValues
