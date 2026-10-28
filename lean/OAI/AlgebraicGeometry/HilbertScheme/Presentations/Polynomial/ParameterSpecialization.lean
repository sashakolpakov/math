import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFamily

/-! # Parameter Specialization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ParameterSpecialization.GradedHilbert

noncomputable section

/-! Specializing the homogeneous coefficients along a map of parameter
schemes produces the same actual relative projective family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) {T : Over S} (x : T ⟶ M)

def parameterHomogeneousIdeal : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(T.left, ⊤) n) :=
  I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap x.left.appTop.hom)

def parameterProjectiveCoefficient :
    Proj (Graded.Quotient.GradedHilbert.quotientGrading (parameterHomogeneousIdeal M I x)) ⟶ Proj (Graded.Quotient.GradedHilbert.quotientGrading I) := by
  let : Algebra Γ(M.left, ⊤) Γ(T.left, ⊤) := x.left.appTop.hom.toAlgebra
  exact Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap I

theorem parameterProjectiveCoefficient_isPullback :
    IsPullback (parameterProjectiveCoefficient M I x)
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (parameterHomogeneousIdeal M I x)))
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) (Spec.map x.left.appTop) := by
  let : Algebra Γ(M.left, ⊤) Γ(T.left, ⊤) := x.left.appTop.hom.toAlgebra
  exact Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback I

def relativePolynomialParameterCoefficient :
    Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily T (parameterHomogeneousIdeal M I x) (𝟙 T) ⟶ Proj (Graded.Quotient.GradedHilbert.quotientGrading I) :=
  pullback.fst _ _ ≫ parameterProjectiveCoefficient M I x

theorem relativePolynomialParameter_isPullback :
    IsPullback (relativePolynomialParameterCoefficient M I x)
      (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection T (parameterHomogeneousIdeal M I x) (𝟙 T))
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) (x.left ≫ M.left.toSpecΓ) := by
  have H := (IsPullback.of_hasPullback
    (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (parameterHomogeneousIdeal M I x)))
      T.left.toSpecΓ).paste_horiz (parameterProjectiveCoefficient_isPullback M I x)
  change IsPullback (relativePolynomialParameterCoefficient M I x)
    (Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection T (parameterHomogeneousIdeal M I x) (𝟙 T))
    (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) (T.left.toSpecΓ ≫ Spec.map x.left.appTop) at H
  rwa [← Scheme.toSpecΓ_naturality x.left] at H

def relativePolynomialParameterIso :
    Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily T (parameterHomogeneousIdeal M I x) (𝟙 T) ≅ Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I x :=
  (relativePolynomialParameter_isPullback M I x).isoPullback

theorem relativePolynomialParameterIso_projection :
    (relativePolynomialParameterIso M I x).hom ≫ Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x =
      Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection T (parameterHomogeneousIdeal M I x) (𝟙 T) :=
  (relativePolynomialParameter_isPullback M I x).isoPullback_hom_snd

theorem relativePolynomialParameterIso_coefficient :
    (relativePolynomialParameterIso M I x).hom ≫ pullback.fst _ _ =
      relativePolynomialParameterCoefficient M I x :=
  (relativePolynomialParameter_isPullback M I x).isoPullback_hom_fst

theorem parameterProjectiveCoefficient_inclusion :
    parameterProjectiveCoefficient M I x ≫ Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (parameterHomogeneousIdeal M I x) ≫
        ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap x.left.appTop.hom := by
  let : Algebra Γ(M.left, ⊤) Γ(T.left, ⊤) := x.left.appTop.hom.toAlgebra
  exact ProjectiveCoefficientMap.GradedHilbert.projectiveCoefficientMap_inclusion I

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ParameterSpecialization.GradedHilbert
