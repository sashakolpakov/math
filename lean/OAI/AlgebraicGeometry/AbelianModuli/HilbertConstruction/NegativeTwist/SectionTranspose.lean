import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameTransposeDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ProjectiveTwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames

/-! # Section Transpose -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.SectionTranspose

noncomputable section

/-! A morphism from a negative projective twist, paired with sections of another sheaf, gives coefficient-linear actual sections of the positive twist. Vanishing is detected by the contracted morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
variable {M N : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules}
variable (β : Bilinear.Sheaves.SheafBilinearMap M N (Line.Bundles.structureModule (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))))
variable (d : ℕ) (φ : (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf ⟶ N)

def negativeTwistSectionTranspose :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj M →ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  Bilinear.FrameSectionTranspose.coefficientPairingFrameSectionMap
    (ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal)
    (β.precomp (𝟙 M) φ) (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))

theorem negativeTwistSectionTranspose_zero_implies
    (s : (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj M)
    (hs : negativeTwistSectionTranspose I β d φ s = 0) :
    φ ≫ β.contractLeft s = 0 := by
  apply (β.contractLeft_precomp (show Γ(M, ⊤) from s) φ).trans
  apply Bilinear.FrameTransposeDetection.contractLeft_eq_zero_of_pairingFrameSectionMap_eq_zero
    (ConstructedCompatibleFrames.openFrameSheafFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal)
    (β.precomp (𝟙 M) φ) (ProjectiveTwisting.Bundle.projectiveTwistingCover I) (show Γ(M, ⊤) from s)
  exact hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.SectionTranspose
