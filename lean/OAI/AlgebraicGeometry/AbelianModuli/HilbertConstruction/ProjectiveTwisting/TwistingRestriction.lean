import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleQuotientTwistingFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteTwistingBundle

/-! # Twisting Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TwistingRestriction

noncomputable section

/-! Restricting the actual ambient projective O(1) to a homogeneous projective quotient gives its constructed degree-one twisting bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def quotientToZeroMorphism : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) :=
  HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left

theorem quotientToZeroMorphism_factor :
    quotientToZeroMorphism I ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I := by
  have he := congrArg Over.Hom.left (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv_hom_id
  have hq : (Projective.QuotientZero.projectiveQuotientZeroIso R n).hom.left =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) := rfl
  have hv : (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left ≫
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) = 𝟙 _ :=
    (congrArg (fun z => (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left ≫ z) hq).symm.trans he
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ z) hv).trans (Category.comp_id _))

def affineProjectiveTwistingBundle_quotientIso :
    ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)).sheaf ≅
      (Bundle.projectiveTwistingBundle I 1).sheaf :=
  (Scheme.Modules.pullbackComp (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left).app
    (Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) 1).sheaf ≪≫
      CompatibleQuotientTwistingFrames.compatibleQuotientTwistingBundleIso I ⊥ (quotientToZeroMorphism I) (quotientToZeroMorphism_factor I)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TwistingRestriction
