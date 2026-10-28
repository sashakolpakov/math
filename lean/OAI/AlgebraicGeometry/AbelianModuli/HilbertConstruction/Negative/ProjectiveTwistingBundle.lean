import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TransitionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle

/-! # Projective Twisting Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ProjectiveTwistingBundle

noncomputable section

/-! Actual negative projective twists are constructed from the reciprocal powers of the projective coordinate transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def negativeProjectiveTwistingBundle (d : ℕ) : Line.Bundles.LineBundle (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :=
  LineBundle.FromOpenFrames.lineBundleFromOpenFrames (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).reciprocal (ProjectiveTwisting.Bundle.projectiveTwistingCover I)

theorem projectiveTwistingTransition_coordinate (d : ℕ) (i j : ULift.{u} (Fin (n + 1))) :
    ((ProjectiveTwisting.Bundle.projectiveTwistingTransitions I d).value
      ((Projective.SectionCover.projectiveCoordinateSectionCover I).overlap i.down j.down) i j inf_le_left inf_le_right).val =
      ((Projective.SectionCover.projectiveCoordinateSectionCover I).transition i.down j.down) ^ d := by
  change ((ProjectiveFrame.Transitions.projectiveFrameTransitions I).value
    ((Projective.SectionCover.projectiveCoordinateSectionCover I).overlap i.down j.down) i.down j.down
      inf_le_left inf_le_right).val ^ d = _
  rw [Projective.TransitionRestriction.projectiveFrameTransition_coordinate]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ProjectiveTwistingBundle
