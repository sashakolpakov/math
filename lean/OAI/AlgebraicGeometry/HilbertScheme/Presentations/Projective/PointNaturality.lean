import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveFunctoriality

/-! # Point Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointNaturality

noncomputable section

/-! Polynomial coordinates at ring-valued scheme points commute with
arbitrary coefficient homomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
variable (a : Spec (CommRingCat.of R) ⟶ S) (φ : R →+* A)

theorem schemePointCoefficientMap_comp_spec :
    PointCoefficients.schemePointCoefficientMap (Spec.map (CommRingCat.ofHom φ) ≫ a) = φ.comp (PointCoefficients.schemePointCoefficientMap a) := by
  have h : CommRingCat.ofHom (PointCoefficients.schemePointCoefficientMap (Spec.map (CommRingCat.ofHom φ) ≫ a)) =
      CommRingCat.ofHom (φ.comp (PointCoefficients.schemePointCoefficientMap a)) := by
    apply Spec.map_injective
    rw [Point.schemePointCoefficientMap_spec, CommRingCat.ofHom_comp, Spec.map_comp,
      Point.schemePointCoefficientMap_spec, Category.assoc]
  exact congrArg CommRingCat.Hom.hom h

namespace GradedHilbert

theorem projectiveSchemePointMap_naturality (n : ℕ) :
    Point.GradedHilbert.projectiveSchemePointMap n (Spec.map (CommRingCat.ofHom φ) ≫ a) =
      Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) φ ≫ Point.GradedHilbert.projectiveSchemePointMap n a := by
  let : Algebra R A := φ.toAlgebra
  apply pullback.hom_ext
  · rw [Point.GradedHilbert.projectiveSchemePointMap_coefficient, Category.assoc, Point.GradedHilbert.projectiveSchemePointMap_coefficient,
      schemePointCoefficientMap_comp_spec, Polynomial.ProjectiveFunctoriality.GradedHilbert.polynomialProjectiveCoefficientMap_comp]
  · change _ ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).hom = (_ ≫ _) ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).hom
    rw [Point.GradedHilbert.projectiveSchemePointMap_projection, Category.assoc, Point.GradedHilbert.projectiveSchemePointMap_projection]
    have h : Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) φ ≫ Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
        Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading A n) ≫ Spec.map (CommRingCat.ofHom φ) := Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjectiveCoefficientMap_over
    simpa only [Category.assoc] using (congrArg (fun f => f ≫ a) h).symm

end GradedHilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointNaturality
