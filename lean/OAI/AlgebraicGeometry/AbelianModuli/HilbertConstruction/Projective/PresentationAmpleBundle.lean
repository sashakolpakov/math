import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Ampleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Presentation Ample Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! Every actual projective presentation over an affine base supplies a concrete ample line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem PresentationAmpleBundle.affineProjectiveTwistingBundle_isAmple (R : Type u) [CommRing R] (n : ℕ) :
    (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).IsAmple := by
  have : IsIso (QuotientZero.projectiveQuotientZeroIso R n).inv.left :=
    (Over.forget (Spec (.of R))).map_isIso (QuotientZero.projectiveQuotientZeroIso R n).inv
  exact (ProjectiveTwisting.Ampleness.projectiveTwistingBundle_one_isAmple (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))).pullback_of_isAffineHom
    (QuotientZero.projectiveQuotientZeroIso R n).inv.left

theorem PresentationAmpleBundle.relativeProjectiveTwistingBundle_isAmple (S : Scheme.{u}) [IsAffine S] (n : ℕ) :
    (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).IsAmple := by
  have : IsAffineHom (Limits.pullback.fst (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ) :=
    MorphismProperty.of_isPullback (CategoryTheory.IsPullback.of_hasPullback
      (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ).flip (inferInstance : IsAffineHom S.toSpecΓ)
  exact (PresentationAmpleBundle.affineProjectiveTwistingBundle_isAmple Γ(S, ⊤) n).pullback_of_isAffineHom
    (Limits.pullback.fst (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ)

variable {S : Scheme.{u}} {X : Over S}

def ProjectivePresentations.ProjectivePresentation.ampleLineBundle (P : ProjectivePresentations.ProjectivePresentation X) : Line.Bundles.LineBundle X.left :=
  (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S P.dimension).pullback P.embedding.left

theorem ProjectivePresentations.ProjectivePresentation.ampleLineBundle_isAmple [IsAffine S] (P : ProjectivePresentations.ProjectivePresentation X) :
    P.ampleLineBundle.IsAmple :=
  (PresentationAmpleBundle.relativeProjectiveTwistingBundle_isAmple S P.dimension).pullback_of_isAffineHom P.embedding.left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
