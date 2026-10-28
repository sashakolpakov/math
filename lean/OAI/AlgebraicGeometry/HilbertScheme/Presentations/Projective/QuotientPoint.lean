import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialCoordinates

/-! # Quotient Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientPoint.GradedHilbert

noncomputable section

/-! The polynomial quotient over a ring-valued point is canonically the
actual relative polynomial fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
variable {R : Type u} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ M.left)

abbrev polynomialPointOver : Over S := Over.mk (a ≫ M.hom)

def polynomialPointMorphism : polynomialPointOver M a ⟶ M := Over.homMk a rfl

def pointHomogeneousIdeal : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (PointCoefficients.schemePointCoefficientMap a))

def projectiveQuotientPointCoefficient :
    Proj (Graded.Quotient.GradedHilbert.quotientGrading (pointHomogeneousIdeal M I a)) ⟶ Quotient.GradedHilbert.projectiveQuotient I := by
  let : Algebra Γ(M.left, ⊤) R := (PointCoefficients.schemePointCoefficientMap a).toAlgebra
  exact CoefficientMap.GradedHilbert.projectiveCoefficientMap I

theorem projectiveQuotientPoint_isPullback :
    IsPullback (projectiveQuotientPointCoefficient M I a)
      (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (pointHomogeneousIdeal M I a)))
      (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) (a ≫ M.left.toSpecΓ) := by
  let : Algebra Γ(M.left, ⊤) R := (PointCoefficients.schemePointCoefficientMap a).toAlgebra
  have H := BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := R) I
  change IsPullback (projectiveQuotientPointCoefficient M I a)
    (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (pointHomogeneousIdeal M I a)))
    (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))
    (Spec.map (CommRingCat.ofHom (PointCoefficients.schemePointCoefficientMap a))) at H
  rwa [Point.schemePointCoefficientMap_spec] at H

def projectiveQuotientPointIso :
    Proj (Graded.Quotient.GradedHilbert.quotientGrading (pointHomogeneousIdeal M I a)) ≅
      Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I (polynomialPointMorphism M a) :=
  (projectiveQuotientPoint_isPullback M I a).isoPullback

theorem projectiveQuotientPointIso_projection :
    (projectiveQuotientPointIso M I a).hom ≫ Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I (polynomialPointMorphism M a) =
      Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (pointHomogeneousIdeal M I a)) :=
  (projectiveQuotientPoint_isPullback M I a).isoPullback_hom_snd

theorem projectiveQuotientPointIso_coefficient :
    (projectiveQuotientPointIso M I a).hom ≫ pullback.fst _ _ = projectiveQuotientPointCoefficient M I a :=
  (projectiveQuotientPoint_isPullback M I a).isoPullback_hom_fst

theorem projectiveQuotientPointCoefficient_inclusion :
    projectiveQuotientPointCoefficient M I a ≫ Quotient.GradedHilbert.projectiveQuotientInclusion I =
      Quotient.GradedHilbert.projectiveQuotientInclusion (pointHomogeneousIdeal M I a) ≫
        Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a) := by
  let : Algebra Γ(M.left, ⊤) R := (PointCoefficients.schemePointCoefficientMap a).toAlgebra
  exact Polynomial.ProjectiveCoefficientMap.GradedHilbert.projectiveCoefficientMap_inclusion I

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientPoint.GradedHilbert
