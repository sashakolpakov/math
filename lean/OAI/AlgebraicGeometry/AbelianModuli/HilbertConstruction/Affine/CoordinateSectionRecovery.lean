import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinateSectionPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteTwistingBundle

/-! # Coordinate Section Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateSectionRecovery

noncomputable section

/-! The actual affine-projective coordinate sections recover the defining
sections under the existing twisting-bundle isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def affineProjectiveCoordinateSection (R : Type u) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    Line.Bundles.structureModule (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶ (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).sheaf :=
  Ample.LineBundles.pullbackSection (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left
    (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) j)

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))

theorem sectionAbsoluteTwistingBundleIso_coordinate (j : Fin (n + 1)) :
    Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (affineProjectiveCoordinateSection Γ(S, ⊤) n j) ≫
        (Section.AbsoluteTwistingBundle.sectionAbsoluteTwistingBundleIso f s hs).hom = s j := by
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let b := (Projective.QuotientZero.projectiveQuotientZeroIso Γ(S, ⊤) n).inv.left
  let q := ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) j
  let e := Section.ProjectiveTwistingFrames.sectionQuotientTwistingBundleIso f s hs ⊥ (Section.AbsoluteTwistingBundle.sectionZeroQuotientMorphism f s hs)
    (Section.AbsoluteTwistingBundle.sectionZeroQuotientMorphism_factor f s hs)
  change Ample.LineBundles.pullbackSection a (Ample.LineBundles.pullbackSection b q) ≫
    ((Scheme.Modules.pullbackComp a b).hom.app _ ≫ e.hom) = s j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom) (Global.SectionPullbackComposition.pullbackSection_composition a b q)).trans
      (Quotient.CoordinateSectionPullback.sectionQuotientTwistingBundleIso_coordinate f s hs ⊥ (Section.AbsoluteTwistingBundle.sectionZeroQuotientMorphism f s hs)
        (Section.AbsoluteTwistingBundle.sectionZeroQuotientMorphism_factor f s hs) j))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateSectionRecovery
