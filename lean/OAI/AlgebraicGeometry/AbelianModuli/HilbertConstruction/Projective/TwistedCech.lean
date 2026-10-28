import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.Bundle

/-! # Twisted Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistedCech

noncomputable section

/-! The coordinate Čech complex of a module tensored with an actual projective twisting line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveTwistedCechFunctor (d : ℕ) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d)).functor ⋙
    CoefficientCechFunctor.projectiveCoefficientCechFunctor I

instance projectiveTwistedCechFunctor_additive (d : ℕ) : (projectiveTwistedCechFunctor I d).Additive := by
  have : (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d)).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp [projectiveTwistedCechFunctor]
  infer_instance

def projectiveTwistedCech (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) (d : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ := (projectiveTwistedCechFunctor I d).obj M

def projectiveTwistedCechActualIso (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) (d : ℕ) :
    projectiveTwistedCech I M d ≅
      (CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (Tensor.ProductSheaf.tensorModule M (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf) :=
  (CoefficientCechFunctor.projectiveCoefficientCechFunctor I).mapIso
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.TwistedCech
