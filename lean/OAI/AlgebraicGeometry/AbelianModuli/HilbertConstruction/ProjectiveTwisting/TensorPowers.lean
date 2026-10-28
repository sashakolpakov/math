import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.FrameRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FirstPowerFrameRealization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

/-! # Tensor Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers

noncomputable section

/-! The constructed degree-d projective twist is the actual dth tensor power of the degree-one twisting line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwistingBundle_tensorPowerIso (d : ℕ) :
    ((Bundle.projectiveTwistingBundle I 1).tensorPower d).sheaf ≅ (Bundle.projectiveTwistingBundle I d).sheaf := by
  let C := (ProjectiveFrame.Transitions.projectiveFrameTransitions I).reindex (ULift.down : ULift.{u} (Fin (n + 1)) → _)
  exact (TensorPower.Maps.tensorPowerFunctor (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) d).mapIso
    (FirstPowerFrameRealization.openFramePowerOneIso C (Bundle.projectiveTwistingCover I)) ≪≫
      TensorPower.FrameRecognition.openFrameTensorPowerIso C (Bundle.projectiveTwistingCover I) d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers
