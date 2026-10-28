import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechHomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechCoproductFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCover

/-! # Negative Twist Cover Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! The constructed finite negative-twist cover has finite Čech cohomology in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} {M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules}

theorem NegativeTwistCover.ProjectiveNegativeTwistCover.source_cech_homology_finite (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) (q : ℕ) :
    Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj D.source).homology q) := by
  let : Finite D.index := D.finite
  exact CechCoproductFiniteness.projectiveCech_homology_finite_coproduct I _ q
    (fun i ↦ NegativeTwist.CechHomologyFiniteness.negativeTwistCech_homology_finite I (D.degree i) q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
