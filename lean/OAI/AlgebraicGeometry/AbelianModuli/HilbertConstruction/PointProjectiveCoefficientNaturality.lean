import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointPolynomialCoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientNaturality

/-! # Point Projective Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointProjectiveCoefficientNaturality

noncomputable section

/-! The actual projective action of a point-coordinate
transformation commutes with coefficient-spectrum base change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

theorem pointCoordinateProjectiveIso_coefficient_natural
    (φ : R →+* A) (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).hom.left ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n ≫ (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom.left := by
  have H : (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) φ).comp
      (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap) =
        (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).toLinearMap).comp
          (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) := by
    apply GradedRingHom.ext
    intro p
    exact RingHom.congr_fun (PointPolynomialCoefficientNaturality.pointCoordinateSubstitution_coefficient_natural φ T) p
  change Proj.map (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).toLinearMap) _ ≫
      Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) _ = Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) _ ≫
        Proj.map (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  exact H.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointProjectiveCoefficientNaturality
