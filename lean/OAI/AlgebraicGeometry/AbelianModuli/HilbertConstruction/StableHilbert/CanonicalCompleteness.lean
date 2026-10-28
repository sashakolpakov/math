import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SectionCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.EmbeddingRecovery

/-! # Canonical Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CanonicalCompleteness.StableHilbertCoverage

noncomputable section

/-! A bijective degree-one polynomial section map supplies the complete
canonical coordinates of the actual quotient projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
variable (hI : Function.Bijective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I 1))

def quotientCoordinateCompleteData : (Affine.CoordinateSectionData.quotientCoordinateSectionData I).CompleteData where
  basis := Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective
    (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).appTop.hom
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I)
    (SectionCompleteness.StableHilbertCoverage.coordinateSections_bijective_of_polynomialMap I hI)
  sections_eq := (Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective_family
    (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).appTop.hom
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I)
    (SectionCompleteness.StableHilbertCoverage.coordinateSections_bijective_of_polynomialMap I hI)).symm

def quotientCanonicalCompleteData :
    (Affine.CoordinateSectionData.quotientCoordinatePresentation I).canonicalSectionData.CompleteData :=
  Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.canonical
    (Affine.CoordinateSectionData.quotientCoordinateSectionData I) (quotientCoordinateCompleteData I hI)

def canonicalCompleteData_of_quotientIso {X : Over (Spec (.of R))}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n) [hi : IsClosedImmersion i.left]
    (e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I ≅ X)
    (he : e.hom ≫ i = (Affine.CoordinateSectionData.quotientCoordinatePresentation I).embedding) :
    (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X).canonicalSectionData.CompleteData := by
  exact @Canonical.EmbeddingRecovery.completeCanonicalData_of_embeddingIso _ _ _ _
    (Affine.CoordinateSectionData.quotientCoordinatePresentation I).embedding i
    (Affine.CoordinateSectionData.quotientCoordinatePresentation I).closedImmersion hi e he (quotientCanonicalCompleteData I hI)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CanonicalCompleteness.StableHilbertCoverage
