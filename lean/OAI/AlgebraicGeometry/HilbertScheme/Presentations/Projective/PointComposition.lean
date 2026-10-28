import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectivePoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveFunctoriality

/-! # Point Composition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointComposition.GradedHilbert

noncomputable section

/-! The canonical projective coordinate comparison respects composition
with an arbitrary morphism of base schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

theorem projectiveSchemePointMap_comp (n : ℕ) (a : Spec (.of R) ⟶ X) (f : X ⟶ Y) :
    Point.GradedHilbert.projectiveSchemePointMap n a ≫ Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap f n =
      Point.GradedHilbert.projectiveSchemePointMap n (a ≫ f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient, ← Category.assoc,
      Point.GradedHilbert.projectiveSchemePointMap_coefficient, Point.GradedHilbert.projectiveSchemePointMap_coefficient]
    have he : PointCoefficients.schemePointCoefficientMap (a ≫ f) =
        (PointCoefficients.schemePointCoefficientMap a).comp f.appTop.hom := rfl
    rw [he, Polynomial.ProjectiveFunctoriality.GradedHilbert.polynomialProjectiveCoefficientMap_comp]
  · change _ ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Y n).hom = _ ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Y n).hom
    rw [Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection, ← Category.assoc,
      Point.GradedHilbert.projectiveSchemePointMap_projection, Point.GradedHilbert.projectiveSchemePointMap_projection, Category.assoc]

theorem globalProjectiveSchemePointMap_eq {S : Scheme.{u}} (M : Over S) (n : ℕ)
    (a : Spec (.of R) ⟶ M.left) :
    Global.ProjectivePoint.GradedHilbert.globalProjectiveSchemePointMap M n a = Point.GradedHilbert.projectiveSchemePointMap n (a ≫ M.hom) :=
  projectiveSchemePointMap_comp n a M.hom

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointComposition.GradedHilbert
