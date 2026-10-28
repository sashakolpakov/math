import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeFamilyModels
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialCoefficients

/-! # Coefficient Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual projective models over finitely generated coefficient subalgebras, with Cartesian recovery of the original family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}
variable {F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)} (E : Single.DegreeFamilyModels.ProjectiveFamilyEquations F)
variable (B : Type v) [CommRing B] [Algebra B R]

def Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientRing : Subalgebra B R := HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert.polynomialCoefficientRing E.polynomial B

instance Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientRing_finiteType : Algebra.FiniteType B (E.coefficientRing B) :=
  HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert.polynomialCoefficientRing_finiteType E.polynomial B

instance Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientRing_noetherian [IsNoetherianRing B] : IsNoetherianRing (E.coefficientRing B) :=
  HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert.polynomialCoefficientRing_isNoetherian E.polynomial B

def Single.DegreeFamilyModels.ProjectiveFamilyEquations.modelIdeal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading (E.coefficientRing B) n) :=
  HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert.polynomialOverCoefficientRing E.polynomial B) E.degree
    (HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert.polynomialOverCoefficientRing_homogeneous E.polynomial B E.degree E.homogeneous)

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.modelIdeal_extension :
    HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B) = E.ideal :=
  HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert.coefficientRing_generatorsIdeal_map E.polynomial B E.degree E.homogeneous

def Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModelIso :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B)) ≅ F.scheme :=
  eqToIso (congrArg Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (E.modelIdeal_extension B)) ≪≫ E.familyIso

def Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModelMap : F.scheme.left ⟶ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (E.modelIdeal B) :=
  (E.coefficientModelIso B).inv.left ≫ HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := R) (E.modelIdeal B)

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModel_isPullback :
    IsPullback (E.coefficientModelMap B) F.scheme.hom
      (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (E.modelIdeal B)))
      (Spec.map (CommRingCat.ofHom (E.coefficientRing B).val.toRingHom)) := by
  let e := E.coefficientModelIso B
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have h : IsPullback e.inv.left F.scheme.hom
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B))).hom
      (𝟙 (Spec (CommRingCat.of R))) :=
    IsPullback.of_horiz_isIso ⟨e.inv.w.trans (Category.comp_id _).symm⟩
  have H := h.paste_horiz (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := R) (E.modelIdeal B))
  simp only [Category.id_comp] at H
  exact H

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModel_proper :
    IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (E.modelIdeal B))) :=
  HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper _

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModel_locallyFinitePresentation [IsNoetherianRing B] :
    LocallyOfFinitePresentation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (E.modelIdeal B))) := by
  let : IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (E.modelIdeal B))) := E.coefficientModel_proper B
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
