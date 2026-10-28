import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechCover

/-! # Coefficient Cech Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechFunctor

noncomputable section

/-! The additive coefficient Cech functor on the projective coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def projectiveCoefficientCechFunctor :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (CechCover.projectiveCechOpens I)

instance projectiveCoefficientCechFunctor_additive : (projectiveCoefficientCechFunctor I).Additive := by
  change (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (CechCover.projectiveCechOpens I)).Additive
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechFunctor
