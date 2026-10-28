import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ProjectiveTwistingBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReciprocalFrameTensorIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstructedCompatibleFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Tensor Inverse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorInverse

noncomputable section

/-! The actual positive and negative projective twists of the same degree are tensor inverses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwisting_positive_negative_iso (d : ℕ) :
    ((Bundle.projectiveTwistingBundle I d).tensor (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d)).sheaf ≅
      Line.Bundles.structureModule (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :=
  (ConstructedCompatibleFrames.openFrameSheafFrames (Bundle.projectiveTwistingTransitions I d)).reciprocalTensorIso
    (ConstructedCompatibleFrames.openFrameSheafFrames (Bundle.projectiveTwistingTransitions I d).reciprocal) (Bundle.projectiveTwistingCover I)

def projectiveTwisting_negative_positive_iso (d : ℕ) :
    ((Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).tensor (Bundle.projectiveTwistingBundle I d)).sheaf ≅
      Line.Bundles.structureModule (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :=
  Tensor.ProductSheaf.tensorModuleCommIso _ _ ≪≫ projectiveTwisting_positive_negative_iso I d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorInverse
