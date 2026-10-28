import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTwistingFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientZero

/-! # Absolute Twisting Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteTwistingBundle

noncomputable section

/-! An actual degree-one twisting line bundle on standard projective space pulls back under every section-defined projective morphism to its source module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def affineProjectiveTwistingBundle (R : Type u) [CommRing R] (n : ℕ) :
    Line.Bundles.LineBundle (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  (ProjectiveTwisting.Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) 1).pullback
    (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))

def sectionZeroQuotientMorphism : X ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n))) :=
  SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).inv.left

theorem sectionZeroQuotientMorphism_factor :
    sectionZeroQuotientMorphism f s hs ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := by
  have he := congrArg Over.Hom.left (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).inv_hom_id
  have hq : (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).hom.left =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) := rfl
  have hv : (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).inv.left ≫
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) = 𝟙 _ :=
    (congrArg (fun z => (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).inv.left ≫ z) hq).symm.trans he
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ z) hv).trans (Category.comp_id _))

def sectionAbsoluteTwistingBundleIso :
    ((affineProjectiveTwistingBundle Γ(S, ⊤) n).pullback (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).sheaf ≅ M :=
  (Scheme.Modules.pullbackComp (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).inv.left).app
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) 1).sheaf ≪≫
    ProjectiveTwistingFrames.sectionQuotientTwistingBundleIso f s hs ⊥ (sectionZeroQuotientMorphism f s hs)
      (sectionZeroQuotientMorphism_factor f s hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteTwistingBundle
